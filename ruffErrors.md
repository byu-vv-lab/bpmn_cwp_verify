# Ruff findings outside generated ANTLR files

## Scope and totals

Scanned the repository with `ruff check .` and `ruff format --check .`, then excluded findings from `src/bpmncwpverify/antlr/`. The remaining lint inventory contains **131 findings across 56 files**. Ruff reports **one file would be reformatted** outside that generated-code directory. The inventory covers the repository root, `src/`, and `test/`.

The prior `TRY002` findings have been replaced with `ErrorException` and typed domain errors; no `TRY002` findings remain in the repository.

Counts below are individual Ruff diagnostics, not distinct files. This report records findings; it does not apply fixes.

## Common patterns

| Rule | Count | What Ruff reports | Examples / concentration |
| --- | ---: | --- | --- |
| EXE002 | 45 | File is marked executable but has no shebang. | Widespread among package modules under `src/bpmncwpverify/`; check whether each file needs its executable bit. |
| TRY002 | 38 | Raise a project-specific exception instead of built-in `Exception`. | `core/bpmn.py`, `core/cwp.py`, `core/expr.py`, `core/frontends/processmethods.py`, and `visitors/bpmnchecks/bpmnvalidations.py`. |
| LOG015 | 12 | Logging calls use the root logger directly. | `src/bpmncwpverify/cli.py`. |
| B018 | 9 | Useless standalone expression. | `test/core/test_spin.py` and `src/bpmncwpverify/core/counterexample.py`. |
| SIM115 | 8 | Use a context manager when opening files. | `test/test_cli.py` and `test/test_lambda_handler.py`. |
| PLW1510 | 7 | `subprocess.run` omits an explicit `check` argument. | `core/cbmc.py`, `core/counterexample.py`, `core/spin.py`, and a builder test. |
| BLE001 | 5 | Catching broad `Exception`. | Includes `lambda_function.py`, `core/expr.py`, `core/typechecking.py`, and tests. |
| PLC0205 | 8 | `__slots__` should be a non-string iterable. | Remaining non-ANTLR string declarations are in `core/error.py`, `visitors/bpmn_graph_visitor.py`, `visitors/bpmnchecks/bpmnvalidations.py`, `visitors/cwp_connectivity_visitor.py`, and `visitors/cwp_graph_visitor.py`. |

## Full lint inventory

| Rule | Count | Description |
| --- | ---: | --- |
| B006 | 1 | Mutable default argument. |
| B017 | 1 | Assertion catches a broad exception. |
| B018 | 9 | Useless standalone expression. |
| B023 | 3 | Nested function does not bind a loop variable. |
| BLE001 | 5 | Broad exception catch. |
| EXE002 | 45 | Executable file has no shebang. |
| ISC004 | 2 | Implicit string concatenation in a collection. |
| LOG015 | 12 | Root logger used directly. |
| PERF102 | 1 | Use dictionary values when keys are unused. |
| PIE790 | 2 | Unnecessary `pass` statement. |
| PLC0205 | 8 | `__slots__` should be a non-string iterable. |
| PLR1716 | 3 | Chained boolean comparison can be simplified. |
| PLW1510 | 7 | `subprocess.run` omits an explicit `check` argument. |
| PYI019 | 2 | Use `Self` instead of a custom `TypeVar`. |
| PYI055 | 2 | Combine repeated `type` members in a union. |
| RUF010 | 3 | Use an explicit conversion flag. |
| RUF012 | 2 | Mutable default value for a class attribute. |
| SIM101 | 1 | Combine repeated `isinstance` checks. |
| SIM102 | 2 | Nested `if` statements can be combined. |
| SIM103 | 1 | Return a condition directly. |
| SIM113 | 2 | Use `enumerate()` for an index loop. |
| SIM114 | 6 | Combine branches with the same body. |
| SIM115 | 8 | Use a context manager when opening files. |
| TRY002 | 38 | Raise a project-specific exception instead of built-in `Exception`. |
| UP047 | 3 | Use type parameters for a generic function. |

## Ruff formatter finding

Outside the excluded ANTLR directory, `ruff format --check .` reports one file:

- `src/bpmncwpverify/core/spin.py`
