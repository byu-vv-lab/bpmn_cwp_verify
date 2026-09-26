#!/usr/bin/env bash

set -Eeuo pipefail

readonly SCRIPT_NAME=${0##*/}
readonly SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
readonly REPO_ROOT=$(cd -- "$SCRIPT_DIR/../.." && pwd -P)
readonly OUTPUT_ROOT="$REPO_ROOT/tmp/run_examples/latest"
readonly PYTHON_COMMAND=${PYTHON_BIN:-python}
readonly VERIFY_CODE='from bpmncwpverify.cli import verify; verify()'

COMPARE_REF=""
TEMP_ROOT=""
BASELINE_TREE=""
WORKTREE_ADDED=0

usage() {
    cat <<EOF
Usage:
  $SCRIPT_NAME
  $SCRIPT_NAME --compare REF
  $SCRIPT_NAME --help

Run every immediate directory under test/resources with both its XML and
Mermaid CWP files. Results are written to tmp/run_examples/latest/.

With --compare, REF is checked out into a detached temporary worktree. Its
verification output is compared with the current working tree without
switching or modifying the current checkout.
EOF
}

die() {
    printf 'error: %s\n' "$*" >&2
    exit 2
}

cleanup() {
    local exit_status=$?

    trap - EXIT
    if ((WORKTREE_ADDED)); then
        git -C "$REPO_ROOT" worktree remove --force "$BASELINE_TREE" \
            >/dev/null 2>&1 || true
    fi
    if [[ -n $TEMP_ROOT && -d $TEMP_ROOT ]]; then
        rm -rf -- "$TEMP_ROOT"
    fi
    exit "$exit_status"
}

trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

parse_arguments() {
    case $# in
        0)
            ;;
        1)
            if [[ $1 == "--help" || $1 == "-h" ]]; then
                usage
                exit 0
            fi
            usage >&2
            exit 2
            ;;
        2)
            if [[ $1 != "--compare" || -z $2 ]]; then
                usage >&2
                exit 2
            fi
            COMPARE_REF=$2
            ;;
        *)
            usage >&2
            exit 2
            ;;
    esac
}

check_prerequisites() {
    [[ -d "$REPO_ROOT/test/resources" ]] || \
        die "test/resources was not found beneath $REPO_ROOT"
    [[ -d "$REPO_ROOT/src/bpmncwpverify" ]] || \
        die "src/bpmncwpverify was not found beneath $REPO_ROOT"
    command -v "$PYTHON_COMMAND" >/dev/null 2>&1 || \
        die "Python executable not found: $PYTHON_COMMAND"
    command -v spin >/dev/null 2>&1 || die "spin executable not found on PATH"

    if [[ -n $COMPARE_REF ]]; then
        command -v git >/dev/null 2>&1 || die "git executable not found on PATH"
        git -C "$REPO_ROOT" rev-parse --is-inside-work-tree >/dev/null 2>&1 || \
            die "$REPO_ROOT is not a Git working tree"
        git -C "$REPO_ROOT" rev-parse --verify --quiet \
            "$COMPARE_REF^{commit}" >/dev/null || \
            die "comparison ref does not resolve to a commit: $COMPARE_REF"
    fi
}

normalize_log() {
    local tree_root=$1
    local raw_log=$2
    local line

    while IFS= read -r line || [[ -n $line ]]; do
        case $line in
            "pan: elapsed time"* | "pan: rate"*)
                continue
                ;;
        esac
        line=${line//"$tree_root"/"<TREE>"}
        printf '%s\n' "$line"
    done <"$raw_log"
}

append_case_artifacts() {
    local tree_root=$1
    local suite_dir=$2
    local example_name=$3
    local format=$4
    local status=$5
    local raw_log=$6
    local relative_log="logs/$example_name/$format.log"

    printf '%s\n' "$status" >"$suite_dir/logs/$example_name/$format.status"
    printf '%s\t%s\t%s\n' \
        "$example_name/$format" "$status" "$relative_log" \
        >>"$suite_dir/summary.tsv"

    {
        printf '=== %s/%s ===\n' "$example_name" "$format"
        printf 'exit_status=%s\n' "$status"
        normalize_log "$tree_root" "$raw_log"
        printf '\n'
    } >>"$suite_dir/snapshot.txt"
}

record_discovery_error() {
    local tree_root=$1
    local suite_dir=$2
    local example_name=$3
    local format=$4
    local message=$5
    local log_dir="$suite_dir/logs/$example_name"
    local raw_log="$log_dir/$format.log"

    mkdir -p -- "$log_dir"
    printf 'ERROR: %s\n' "$message" >"$raw_log"
    append_case_artifacts \
        "$tree_root" "$suite_dir" "$example_name" "$format" 2 "$raw_log"
    printf '  [ERROR] %s/%s: %s\n' "$example_name" "$format" "$message" >&2
}

run_case() {
    local tree_root=$1
    local suite_dir=$2
    local example_name=$3
    local format=$4
    local state_file=$5
    local cwp_file=$6
    local bpmn_file=$7
    local log_dir="$suite_dir/logs/$example_name"
    local raw_log="$log_dir/$format.log"
    local status

    mkdir -p -- "$log_dir"
    printf '  [RUN] %s/%s\n' "$example_name" "$format"

    if (
        cd -- "$tree_root"
        export PYTHONDONTWRITEBYTECODE=1
        export PYTHONPATH="$tree_root/src${PYTHONPATH:+:$PYTHONPATH}"
        "$PYTHON_COMMAND" -c "$VERIFY_CODE" \
            "$state_file" "$cwp_file" "$bpmn_file"
    ) >"$raw_log" 2>&1; then
        status=0
    else
        status=$?
    fi

    append_case_artifacts \
        "$tree_root" "$suite_dir" "$example_name" "$format" "$status" "$raw_log"

    if ((status == 0)); then
        printf '  [DONE] %s/%s\n' "$example_name" "$format"
        return 0
    fi

    printf '  [FAIL] %s/%s exited with status %d\n' \
        "$example_name" "$format" "$status" >&2
    return 1
}

run_suite() {
    local tree_root=$1
    local suite_dir=$2
    local suite_label=$3
    local resources_dir="$tree_root/test/resources"
    local example_dir
    local example_name
    local state_path
    local state_file
    local bpmn_file
    local xml_file
    local mmd_file
    local common_error
    local xml_error
    local mmd_error
    local suite_failed=0
    local case_count=0
    local -a bpmn_candidates
    local -a xml_candidates

    mkdir -p -- "$suite_dir/logs"
    printf 'case\texit_status\tlog\n' >"$suite_dir/summary.tsv"
    : >"$suite_dir/snapshot.txt"

    printf 'Running examples for %s\n' "$suite_label"

    while IFS= read -r -d '' example_dir; do
        example_name=${example_dir##*/}
        state_path="$example_dir/state.txt"
        state_file="test/resources/$example_name/state.txt"
        bpmn_file=""
        xml_file=""
        mmd_file="test/resources/$example_name/cwp.mmd"
        common_error=""
        xml_error=""
        mmd_error=""

        if [[ ! -f $state_path ]]; then
            common_error="missing state.txt"
        fi

        shopt -s nullglob
        bpmn_candidates=("$example_dir"/workflow*.bpmn)
        shopt -u nullglob
        if ((${#bpmn_candidates[@]} == 1)); then
            bpmn_file="test/resources/$example_name/${bpmn_candidates[0]##*/}"
        elif ((${#bpmn_candidates[@]} > 1)); then
            common_error="${common_error:+$common_error; }multiple workflow*.bpmn files"
        elif [[ -f "$example_dir/test_bpmn.bpmn" ]]; then
            bpmn_file="test/resources/$example_name/test_bpmn.bpmn"
        else
            common_error="${common_error:+$common_error; }missing workflow*.bpmn or test_bpmn.bpmn"
        fi

        if [[ -f "$example_dir/cwp.xml" ]]; then
            xml_file="test/resources/$example_name/cwp.xml"
        else
            shopt -s nullglob
            xml_candidates=("$example_dir"/*_cwp.xml)
            shopt -u nullglob
            if ((${#xml_candidates[@]} == 1)); then
                xml_file="test/resources/$example_name/${xml_candidates[0]##*/}"
            elif ((${#xml_candidates[@]} > 1)); then
                xml_error="multiple *_cwp.xml fallback files"
            else
                xml_error="missing cwp.xml or a unique *_cwp.xml fallback"
            fi
        fi

        if [[ ! -f "$example_dir/cwp.mmd" ]]; then
            mmd_error="missing cwp.mmd"
        fi

        if [[ -n $common_error ]]; then
            record_discovery_error \
                "$tree_root" "$suite_dir" "$example_name" xml "$common_error"
            record_discovery_error \
                "$tree_root" "$suite_dir" "$example_name" mmd "$common_error"
            suite_failed=1
        else
            if [[ -n $xml_error ]]; then
                record_discovery_error \
                    "$tree_root" "$suite_dir" "$example_name" xml "$xml_error"
                suite_failed=1
            elif ! run_case \
                "$tree_root" "$suite_dir" "$example_name" xml \
                "$state_file" "$xml_file" "$bpmn_file"; then
                suite_failed=1
            fi

            if [[ -n $mmd_error ]]; then
                record_discovery_error \
                    "$tree_root" "$suite_dir" "$example_name" mmd "$mmd_error"
                suite_failed=1
            elif ! run_case \
                "$tree_root" "$suite_dir" "$example_name" mmd \
                "$state_file" "$mmd_file" "$bpmn_file"; then
                suite_failed=1
            fi
        fi

        case_count=$((case_count + 2))
    done < <(
        find "$resources_dir" -mindepth 1 -maxdepth 1 -type d -print0 | sort -z
    )

    if ((case_count == 0)); then
        printf 'error: no example directories found beneath %s\n' "$resources_dir" >&2
        return 1
    fi

    printf 'total_cases\t%d\n' "$case_count" >>"$suite_dir/summary.tsv"
    printf 'total_cases=%d\n' "$case_count" >>"$suite_dir/snapshot.txt"
    printf 'Completed %d cases for %s\n' "$case_count" "$suite_label"
    return "$suite_failed"
}

main() {
    local current_status=0
    local baseline_status=0
    local comparison_status=0
    local resolved_ref
    local comparison_diff="$OUTPUT_ROOT/comparison.diff"

    parse_arguments "$@"
    check_prerequisites

    rm -rf -- "$OUTPUT_ROOT"
    mkdir -p -- "$OUTPUT_ROOT/current"

    if ! run_suite "$REPO_ROOT" "$OUTPUT_ROOT/current" "current working tree"; then
        current_status=1
    fi

    if [[ -n $COMPARE_REF ]]; then
        resolved_ref=$(git -C "$REPO_ROOT" rev-parse --verify "$COMPARE_REF^{commit}")
        TEMP_ROOT=$(mktemp -d "${TMPDIR:-/tmp}/run-examples.XXXXXX")
        BASELINE_TREE="$TEMP_ROOT/worktree"

        printf 'Creating detached worktree for %s (%s)\n' \
            "$COMPARE_REF" "${resolved_ref:0:12}"
        git -C "$REPO_ROOT" worktree add --detach "$BASELINE_TREE" "$resolved_ref" \
            >/dev/null
        WORKTREE_ADDED=1

        mkdir -p -- "$OUTPUT_ROOT/baseline"
        if ! run_suite \
            "$BASELINE_TREE" "$OUTPUT_ROOT/baseline" "$COMPARE_REF baseline"; then
            baseline_status=1
        fi

        if diff -u \
            --label "$COMPARE_REF (baseline)" \
            --label "current working tree" \
            "$OUTPUT_ROOT/baseline/snapshot.txt" \
            "$OUTPUT_ROOT/current/snapshot.txt" \
            >"$comparison_diff"; then
            printf '\nComparison with this branch matches %s!\n' "$COMPARE_REF"
        else
            comparison_status=$?
            if ((comparison_status == 1)); then
                printf 'Comparison differs from %s; see %s\n' \
                    "$COMPARE_REF" "${comparison_diff#"$REPO_ROOT/"}" >&2
            else
                printf '\nerror: diff failed with status %d\n' "$comparison_status" >&2
            fi
        fi
    fi

    printf '\nResults Stored: %s\n' "${OUTPUT_ROOT#"$REPO_ROOT/"}"
    printf '%s\n' \
        'Inspect the captured logs and comparison diff here.'

    if ((current_status != 0 || baseline_status != 0 || comparison_status != 0)); then
        return 1
    fi
    return 0
}

main "$@"
