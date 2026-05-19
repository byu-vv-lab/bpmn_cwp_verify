"""
parse_cbmc_xml.py — CBMC --xml-ui counterexample parser
========================================================
Filters the raw XML from `cbmc --xml-ui` into a readable counterexample report.

Usage:
    cbmc face2face_cbmc_bug.c --unwind 26 --xml-ui > out.xml
    python parse_cbmc_xml.py out.xml
"""

import sys
import xml.etree.ElementTree as ET

# ---------------------------------------------------------------------------
# Face-to-face transition map (choice ID -> name)
# In cbmc_builder.py this will be generated alongside the C file.
# ---------------------------------------------------------------------------

ID_TO_NAME = {
    0: "T_BUYER_START",
    1: "T_SELLER_START",
    2: "T_MEET",
    3: "T_GW_BOTH",
    4: "T_TASK2_TERMS",
    5: "T_TASK3_PRICE",
    6: "T_GW_BOTH_JOIN",
    7: "T_GW_DEC_AGREED",
    8: "T_GW_DEC_RETRY",
    9: "T_TASK4_COUNTEROFFER",
    10: "T_TASK5_RESPOND",
    11: "T_GW_RESP_ACCEPTED",
    12: "T_GW_RESP_REJECTED",
    13: "T_GW_RETRY_JOIN",
    14: "T_TASK6_HANDSHAKE",
    15: "T_GW_EXCH_SPLIT",
    16: "T_TASK7A_PAYMENT",
    17: "T_TASK7B_BACKPACK",
    18: "T_GW_EXCH_JOIN",
    19: "T_END_COMPLETED",
    20: "T_END_FAILED",
}

CWP_NAMES = {
    0: "Init",
    1: "Negotiations",
    2: "Agreed",
    3: "Failed",
    4: "Switched",
}

# Human-readable display values for domain variables.
# Keeps the report readable without needing to look up #define values.
VALUE_DISPLAY = {
    "paymentOwner": {0: "BUYER", 1: "SELLER"},
    "backpackOwner": {0: "BUYER", 1: "SELLER"},
    "terms": {0: "AGREED", 1: "PENDING"},
}

# ---------------------------------------------------------------------------
# Noise filtering
# ---------------------------------------------------------------------------

# Variable name prefixes that are pure mechanics — never domain-relevant.
#   en_*          enable variables (transition scheduling)
#   e_*           edge guard conditions (update_cwp_state inputs)
#   p_*           place tokens (Petri net token booleans)
#   old / next    update_cwp_state internal arrays
#   cwp_reached   reachability tracking booleans (not CWP state itself)
#   __CPROVER     CBMC internal
#   return_value  nondet return bookkeeping
#   loop_bound    CBMC loop bounding
NOISE_PREFIXES = (
    "en_",
    "e_",
    "p_",
    "old",
    "next",
    "cwp_reached",
    "__CPROVER",
    "return_value",
    "loop_bound",
)

# Single-variable exact-match noise: loop counters and internal step tracking.
NOISE_EXACT = {"i", "active", "step", "t"}


def is_noise(lhs):
    if lhs in NOISE_EXACT:
        return True
    return any(lhs.startswith(p) for p in NOISE_PREFIXES)


def is_cwp_state(lhs):
    """True for cwp[Nl] — the active CWP state array (not cwp_reached)."""
    return lhs.startswith("cwp[") and lhs.endswith("l]")


def cwp_index(lhs):
    try:
        return int(lhs[4 : lhs.index("l")])
    except (ValueError, IndexError):
        return None


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------


def parse_trace(trace_elem):
    """
    Walk a <goto_trace> and return one dict per transition.

    Key insight: CBMC re-emits ALL visible state at every step, not just
    changes. We track last_seen values and only report a variable when its
    value actually changed this transition.
    """
    transitions = []
    current_name = None
    current_changes = []  # (lhs, display_value) pairs
    current_cwp = []  # "StateA → StateB" strings
    prev_active_cwp = None
    is_violation = False
    last_seen = {}  # lhs -> last raw value (for delta detection)

    def commit():
        nonlocal current_name, current_changes, current_cwp, is_violation
        if current_name is not None:
            transitions.append(
                {
                    "name": current_name,
                    "changes": current_changes,
                    "cwp": current_cwp,
                    "violation": is_violation,
                }
            )
        current_name = None
        current_changes = []
        current_cwp = []
        is_violation = False

    for child in trace_elem:
        if child.tag == "assignment":
            if child.get("hidden") == "true":
                continue

            lhs = (child.findtext("full_lhs") or "").strip()
            val = (child.findtext("full_lhs_value") or "").strip()

            # --- Transition boundary ---
            if lhs == "choice":
                commit()
                try:
                    choice_id = int(val)
                except ValueError:
                    choice_id = -1
                current_name = ID_TO_NAME.get(choice_id, f"transition_{choice_id}")
                continue

            if current_name is None:
                continue  # assignments before first choice

            # --- Drop noise ---
            if is_noise(lhs):
                continue

            # --- CWP state transitions ---
            if is_cwp_state(lhs):
                if val.upper() in ("TRUE", "1") and last_seen.get(lhs) != val:
                    idx = cwp_index(lhs)
                    state_name = (
                        CWP_NAMES.get(idx, f"cwp[{idx}]") if idx is not None else lhs
                    )
                    if prev_active_cwp is not None and prev_active_cwp != idx:
                        from_name = CWP_NAMES.get(
                            prev_active_cwp, f"cwp[{prev_active_cwp}]"
                        )
                        current_cwp.append(f"{from_name} → {state_name}")
                    prev_active_cwp = idx
                last_seen[lhs] = val
                continue

            # --- Delta check: only report if value actually changed ---
            if last_seen.get(lhs) == val:
                continue
            last_seen[lhs] = val

            # --- Format value for display ---
            display_val = val
            try:
                int_val = int(val)
                display_val = VALUE_DISPLAY.get(lhs, {}).get(int_val, val)
            except ValueError:
                pass

            current_changes.append(f"{lhs}={display_val}")

        elif child.tag == "failure":
            is_violation = True

    commit()
    return transitions


# ---------------------------------------------------------------------------
# Formatter
# ---------------------------------------------------------------------------


def format_report(results):
    lines = []
    for res in results:
        lines.append("=" * 60)
        lines.append("PROPERTY VIOLATED")
        lines.append(f"  {res['description']}")
        lines.append(f"  {res['location']}")
        lines.append("")
        lines.append(f"Counterexample — {len(res['transitions'])} transitions:")
        lines.append("")

        for i, t in enumerate(res["transitions"], 1):
            marker = "  ← VIOLATION" if t["violation"] else ""

            if not t["changes"] and not t["cwp"]:
                lines.append(f"  {i:2d}. {t['name']:<32}  [no domain changes]{marker}")
                continue

            # First line: transition name + first change (or CWP)
            all_parts = list(t["changes"])
            for cwp in t["cwp"]:
                all_parts.append(f"CWP: {cwp}")

            lines.append(f"  {i:2d}. {t['name']:<32}  {all_parts[0]}{marker}")
            indent = " " * (6 + 32)
            for part in all_parts[1:]:
                lines.append(f"{indent}  {part}")

        lines.append("")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main():
    if len(sys.argv) < 2:
        print("Usage: python parse_cbmc_xml.py <cbmc_xml_output_file>")
        sys.exit(1)

    with open(sys.argv[1]) as f:
        xml_text = f.read()

    root = ET.fromstring(xml_text)

    failures = []
    for result in root.findall(".//result[@status='FAILURE']"):
        description = (result.findtext("description") or "").strip()
        loc = result.find("location")
        location = ""
        if loc is not None:
            location = f"{loc.get('file', '')} line {loc.get('line', '')}"

        trace = result.find("goto_trace")
        if trace is None:
            continue

        transitions = parse_trace(trace)
        failures.append(
            {
                "description": description,
                "location": location,
                "transitions": transitions,
            }
        )

    if not failures:
        print("VERIFICATION SUCCESSFUL — no property violations found.")
        return

    print(format_report(failures))


if __name__ == "__main__":
    main()
