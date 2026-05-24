# type: ignore
"""
Integration tests for CbmcBuilder — end-to-end C generation from real test fixtures.

Run with:
    pytest test/builder/test_cbmc_builder.py -v

To also run the CBMC verification step, install cbmc and run:
    pytest test/builder/test_cbmc_builder.py -v -m cbmc
"""

import shutil
import subprocess
import tempfile
from pathlib import Path

import pytest
from returns.pipeline import is_successful
from returns.unsafe import unsafe_perform_io

from bpmncwpverify.builder.cbmc_builder import CbmcBuilder
from bpmncwpverify.core.accessmethods import bpmnmethods
from bpmncwpverify.core.accessmethods.cwpmethods import CwpXmlParser
from bpmncwpverify.core.error import get_error_message
from bpmncwpverify.core.state import State
from bpmncwpverify.util.file import element_tree_from_string, read_file_as_string

# ── Helpers ────────────────────────────────────────────────────────────────────

RESOURCES = Path(__file__).parent.parent / "resources"
SIMPLE = RESOURCES / "simple_example"
FACE2FACE = RESOURCES / "face2face"


def _build_c(state_path: Path, cwp_path: Path, bpmn_path: Path) -> str:
    """Run the full parse+build pipeline and return the generated C string."""
    state_str_io = read_file_as_string(str(state_path))
    state_str = unsafe_perform_io(state_str_io.unwrap())

    cwp_str_io = read_file_as_string(str(cwp_path))
    cwp_str = unsafe_perform_io(cwp_str_io.unwrap())

    bpmn_str_io = read_file_as_string(str(bpmn_path))
    bpmn_str = unsafe_perform_io(bpmn_str_io.unwrap())

    state_result = State.from_str(state_str)
    assert is_successful(state_result), get_error_message(state_result.failure())
    state = state_result.unwrap()

    cwp_xml_io = element_tree_from_string(cwp_str)
    cwp_xml = unsafe_perform_io(cwp_xml_io.unwrap())

    bpmn_xml_io = element_tree_from_string(bpmn_str)
    bpmn_xml = unsafe_perform_io(bpmn_xml_io.unwrap())

    cwp_result = CwpXmlParser.from_xml(cwp_xml, state)
    assert is_successful(cwp_result), get_error_message(cwp_result.failure())
    cwp = cwp_result.unwrap()

    bpmn_result = bpmnmethods.from_xml(bpmn_xml, state)
    assert is_successful(bpmn_result), get_error_message(bpmn_result.failure())
    bpmn = bpmn_result.unwrap()

    c_result = CbmcBuilder().with_state(state).with_cwp(cwp).with_bpmn(bpmn).build()
    assert is_successful(c_result), get_error_message(c_result.failure())
    return c_result.unwrap()


# ── simple_example tests ────────────────────────────────────────────────────────


class TestSimpleExampleGeneration:
    """Tests for C generation from simple_example (single loop, one var)."""

    @pytest.fixture(scope="class")
    def c_code(self):
        return _build_c(
            SIMPLE / "state.txt",
            SIMPLE / "cwp.xml",
            SIMPLE / "workflow.bpmn",
        )

    def test_produces_non_empty_output(self, c_code):
        assert len(c_code) > 100

    def test_includes_stdbool(self, c_code):
        assert "#include <stdbool.h>" in c_code

    def test_nondet_int_declaration(self, c_code):
        assert "int nondet_int();" in c_code

    # ── BOUND ──

    def test_bound_defined(self, c_code):
        assert "#define BOUND" in c_code

    def test_bound_is_20(self, c_code):
        # 5 transitions × 4 = 20
        import re

        assert re.search(r"#define BOUND\s+20\b", c_code), (
            "Expected BOUND == 20 (5 transitions × 4)"
        )

    # ── CWP state defines ──

    def test_cwp_start_defined(self, c_code):
        assert "#define CWP_START" in c_code

    def test_cwp_increment_x_defined(self, c_code):
        assert "#define CWP_INCREMENT_X" in c_code

    def test_cwp_end_defined(self, c_code):
        assert "#define CWP_END" in c_code

    def test_cwp_num_states_is_3(self, c_code):
        # 3 states: Start (gets Init_Edge so has in_edges), Increment_x, End
        import re

        assert re.search(r"#define CWP_NUM_STATES\s+3\b", c_code), (
            "Expected CWP_NUM_STATES == 3"
        )

    # ── Transition defines ──

    def test_transition_start_event(self, c_code):
        assert "#define T_StartEvent_1" in c_code

    def test_transition_task(self, c_code):
        assert "#define T_Task_1" in c_code

    def test_transition_flow3_xor_branch(self, c_code):
        # XOR gateway → one T_ per outgoing flow
        assert "#define T_Flow_3" in c_code

    def test_transition_flow4_xor_branch(self, c_code):
        assert "#define T_Flow_4" in c_code

    def test_transition_end_event(self, c_code):
        assert "#define T_EndEvent_1" in c_code

    def test_five_transitions_total(self, c_code):
        import re

        count = len(re.findall(r"^#define T_", c_code, re.MULTILINE))
        assert count == 5, f"Expected 5 transition defines, got {count}"

    # ── update_cwp_state function ──

    def test_update_cwp_state_signature(self, c_code):
        assert (
            "static void update_cwp_state(int *cwp_state, bool cwp_reached[], int x)"
            in c_code
        )

    def test_cwp_edge_conditions_present(self, c_code):
        assert "e_UNKNOWN_to_Start" in c_code
        assert "e_Start_to_Increment_x" in c_code
        assert "e_Increment_x_to_End" in c_code

    def test_cwp_edge_expressions(self, c_code):
        assert "(x == 0)" in c_code  # Init_Edge
        assert "(x <= 5)" in c_code  # Start → Increment_x
        assert "(x > 5)" in c_code  # Increment_x → End

    def test_next_state_booleans(self, c_code):
        assert "next_Start" in c_code
        assert "next_Increment_x" in c_code
        assert "next_End" in c_code

    def test_p1_assertion_present(self, c_code):
        assert "__CPROVER_assert" in c_code
        assert "CWP P1: transition follows valid CWP edge" in c_code

    # ── main() structure ──

    def test_var_x_declared(self, c_code):
        assert "int x = 0;" in c_code

    def test_token_places_present(self, c_code):
        assert "bool p_StartEvent_1 = true;" in c_code
        assert "bool p_Task_1_FROM_StartEvent_1 = false;" in c_code
        assert "bool p_Gateway_1_FROM_Task_1 = false;" in c_code
        assert "bool p_EndEvent_1_FROM_Gateway_1 = false;" in c_code
        assert "bool p_Task_1_FROM_Gateway_1 = false;" in c_code

    def test_cwp_initial_state(self, c_code):
        # Initial tracking state = dest of start_state's first out_edge = Increment_x
        assert "int cwp_state = CWP_INCREMENT_X;" in c_code

    def test_cwp_reached_initializer(self, c_code):
        # index 0 (CWP_START) = false, index 1 (CWP_INCREMENT_X) = true, index 2 (CWP_END) = false
        assert "cwp_reached[CWP_NUM_STATES] = {false, true, false};" in c_code

    def test_while_loop_with_bound(self, c_code):
        assert "while (running && step < BOUND)" in c_code

    def test_cprover_assume_present(self, c_code):
        assert "__CPROVER_assume(" in c_code

    def test_task_behavior_executed(self, c_code):
        assert "x = x + 1;" in c_code

    def test_update_cwp_state_called_after_task(self, c_code):
        assert "update_cwp_state(&cwp_state, cwp_reached, x);" in c_code

    def test_end_event_sets_running_false(self, c_code):
        assert "running = false;" in c_code

    def test_end_event_reachability_var(self, c_code):
        assert "EndEvent_1_reached = true;" in c_code

    def test_reachability_ifdef_block(self, c_code):
        assert "#ifdef REACHABILITY" in c_code
        assert "__CPROVER_cover(EndEvent_1_reached);" in c_code

    def test_returns_zero(self, c_code):
        assert "return 0;" in c_code

    # ── File write round-trip ──

    def test_write_to_file(self, c_code):
        with tempfile.NamedTemporaryFile(suffix=".c", mode="w", delete=False) as f:
            f.write(c_code)
            path = f.name
        assert Path(path).stat().st_size > 0


# ── CBMC execution tests (require cbmc to be installed) ────────────────────────


@pytest.mark.cbmc
class TestSimpleExampleCbmc:
    """Runs the actual CBMC tool. Only executed with: pytest -m cbmc"""

    @pytest.fixture(scope="class")
    def c_file(self):
        c_code = _build_c(
            SIMPLE / "state.txt",
            SIMPLE / "cwp.xml",
            SIMPLE / "workflow.bpmn",
        )
        with tempfile.NamedTemporaryFile(suffix=".c", mode="w", delete=False) as f:
            f.write(c_code)
            return Path(f.name)

    def test_cbmc_installed(self):
        assert shutil.which("cbmc") is not None, (
            "cbmc not found in PATH — install with: brew install cbmc"
        )

    def test_cbmc_verification_successful(self, c_file):
        """BOUND=20, --unwind 21 covers the loop termination check."""
        result = subprocess.run(
            ["cbmc", str(c_file), "--unwind", "21"],
            capture_output=True,
            text=True,
        )
        assert "VERIFICATION SUCCESSFUL" in result.stdout, (
            f"CBMC failed.\nSTDOUT:\n{result.stdout}\nSTDERR:\n{result.stderr}"
        )

    def test_cbmc_reachability(self, c_file):
        """All CWP states and the end event must be reachable."""
        result = subprocess.run(
            [
                "cbmc",
                str(c_file),
                "--unwind",
                "21",
                "--cover",
                "cover",
                "-DREACHABILITY",
            ],
            capture_output=True,
            text=True,
        )
        # Expect: 4 of 4 covered (EndEvent_1 + CWP_START + CWP_INCREMENT_X + CWP_END)
        assert "4 of 4" in result.stdout or "COVERED" in result.stdout, (
            f"Reachability incomplete.\nSTDOUT:\n{result.stdout}\nSTDERR:\n{result.stderr}"
        )
