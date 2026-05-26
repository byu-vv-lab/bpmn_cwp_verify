# type: ignore
"""
Unit tests for CwpCbmcVisitor.

Follows the same mock-heavy pattern used in test_cwp_promela_visitor.py —
CwpState and CwpEdge objects are mocked rather than parsed from XML.
"""

import pytest

from bpmncwpverify.core.cwp import Cwp, CwpEdge, CwpState
from bpmncwpverify.visitors.cwp_cbmc_visitor import CwpCbmcVisitor

# ── helpers ───────────────────────────────────────────────────────────────────


def make_state(mocker, name: str, sid: str, in_edges=None, out_edges=None):
    state = mocker.Mock(spec=CwpState)
    state.id = sid
    state.name = name
    state.in_edges = in_edges or []
    state.out_edges = out_edges or []
    return state


def make_edge(mocker, eid: str, expression: str, source=None, dest=None):
    edge = mocker.Mock(spec=CwpEdge)
    edge.id = eid
    edge.expression = expression
    edge.source = source
    edge.dest = dest
    return edge


@pytest.fixture
def visitor():
    return CwpCbmcVisitor()


# ── name helpers ──────────────────────────────────────────────────────────────


def test_define_name(visitor, mocker):
    state = make_state(mocker, "Increment_x", "s1")
    assert visitor._define_name(state) == "CWP_INCREMENT_X"


def test_edge_cond_var_with_source(visitor, mocker):
    src = make_state(mocker, "Start", "s0")
    dst = make_state(mocker, "Increment_x", "s1")
    edge = make_edge(mocker, "e1", "x <= 5", source=src, dest=dst)
    assert visitor._edge_cond_var(edge) == "e_Start_to_Increment_x"


def test_edge_cond_var_no_source(visitor, mocker):
    dst = make_state(mocker, "Start", "s0")
    edge = make_edge(mocker, "e0", "x == 0", source=None, dest=dst)
    assert visitor._edge_cond_var(edge) == "e_UNKNOWN_to_Start"


# ── mapping function ──────────────────────────────────────────────────────────


def test_mapping_function_with_in_and_out_edges(visitor, mocker):
    src = make_state(mocker, "Start", "s0")
    mid = make_state(mocker, "Mid", "s1")
    dst = make_state(mocker, "End", "s2")
    e_in = make_edge(mocker, "e1", "x <= 5", source=src, dest=mid)
    e_out = make_edge(mocker, "e2", "x > 5", source=mid, dest=dst)
    mid.in_edges = [e_in]
    mid.out_edges = [e_out]
    result = visitor._mapping_function(mid)
    assert result == "(e_Start_to_Mid) && !(e_Mid_to_End)"


def test_mapping_function_terminal_state(visitor, mocker):
    src = make_state(mocker, "Mid", "s1")
    end = make_state(mocker, "End", "s2")
    e_in = make_edge(mocker, "e2", "x > 5", source=src, dest=end)
    end.in_edges = [e_in]
    end.out_edges = []
    result = visitor._mapping_function(end)
    assert result == "(e_Mid_to_End) && !(false)"


def test_mapping_function_no_in_edges(visitor, mocker):
    state = make_state(mocker, "Start", "s0")
    state.in_edges = []
    state.out_edges = []
    result = visitor._mapping_function(state)
    assert result == "(true) && !(false)"


# ── visitor callbacks ─────────────────────────────────────────────────────────


def test_visit_cwp_sets_init_state(visitor, mocker):
    model = mocker.Mock(spec=Cwp)
    start = make_state(mocker, "Start", "s0")
    init = make_state(mocker, "Increment_x", "s1")
    edge = make_edge(mocker, "e0", "x == 0", source=None, dest=init)
    start.out_edges = [edge]
    model.start_state = start
    visitor.visit_cwp(model)
    assert visitor._init_state is init
    assert visitor._cwp_start_state is start


def test_visit_state_with_in_edges_is_tracked(visitor, mocker):
    e = make_edge(mocker, "e1", "x > 0")
    state = make_state(mocker, "Mid", "s1", in_edges=[e], out_edges=[])
    e.source = mocker.Mock()
    e.dest = state
    visitor.visit_state(state)
    assert state in visitor._states


def test_visit_state_without_in_edges_not_tracked(visitor, mocker):
    state = make_state(mocker, "Start", "s0", in_edges=[], out_edges=[])
    visitor.visit_state(state)
    assert state not in visitor._states


def test_visit_state_deduplicates(visitor, mocker):
    e = make_edge(mocker, "e1", "x > 0")
    state = make_state(mocker, "Mid", "s1", in_edges=[e])
    e.dest = state
    visitor.visit_state(state)
    visitor.visit_state(state)
    assert visitor._states.count(state) == 1


def test_visit_state_collects_edges(visitor, mocker):
    e_in = make_edge(mocker, "e1", "x <= 5")
    e_out = make_edge(mocker, "e2", "x > 5")
    e_in.dest = mocker.Mock()
    e_out.dest = mocker.Mock()
    state = make_state(mocker, "Mid", "s1", in_edges=[e_in], out_edges=[e_out])
    visitor.visit_state(state)
    assert "e1" in visitor._edges
    assert "e2" in visitor._edges


# ── public properties ─────────────────────────────────────────────────────────


def test_num_states(visitor, mocker):
    e = make_edge(mocker, "e1", "x > 0")
    s = make_state(mocker, "Mid", "s1", in_edges=[e])
    e.dest = s
    visitor.visit_state(s)
    assert visitor.num_states == 1


def test_state_define_names(visitor, mocker):
    e1 = make_edge(mocker, "e1", "x > 0")
    e2 = make_edge(mocker, "e2", "x > 5")
    s1 = make_state(mocker, "Increment_x", "s1", in_edges=[e1])
    s2 = make_state(mocker, "End", "s2", in_edges=[e2])
    e1.dest = s1
    e2.dest = s2
    visitor._states = [s1, s2]
    assert visitor.state_define_names() == ["CWP_INCREMENT_X", "CWP_END"]


def test_reachable_state_define_names_excludes_start(visitor, mocker):
    e1 = make_edge(mocker, "e0", "x == 0")
    start = make_state(mocker, "Start", "s0", in_edges=[e1])
    e2 = make_edge(mocker, "e1", "x <= 5")
    mid = make_state(mocker, "Increment_x", "s1", in_edges=[e2])
    e1.dest = start
    e2.dest = mid
    visitor._states = [start, mid]
    visitor._cwp_start_state = start
    names = visitor.reachable_state_define_names()
    assert "CWP_START" not in names
    assert "CWP_INCREMENT_X" in names


def test_initial_cwp_state_define(visitor, mocker):
    e = make_edge(mocker, "e1", "x <= 5")
    init = make_state(mocker, "Increment_x", "s1", in_edges=[e])
    e.dest = init
    visitor._states = [init]
    visitor._init_state = init
    assert visitor.initial_cwp_state_define() == "CWP_INCREMENT_X"


def test_cwp_reached_init_expr(visitor, mocker):
    e1 = make_edge(mocker, "e0", "x == 0")
    s0 = make_state(mocker, "Start", "s0", in_edges=[e1])
    e2 = make_edge(mocker, "e1", "x <= 5")
    s1 = make_state(mocker, "Increment_x", "s1", in_edges=[e2])
    e3 = make_edge(mocker, "e2", "x > 5")
    s2 = make_state(mocker, "End", "s2", in_edges=[e3])
    visitor._states = [s0, s1, s2]
    visitor._init_state = s1
    assert visitor.cwp_reached_init_expr() == "{false, true, false}"


# ── code generation ───────────────────────────────────────────────────────────


def test_generate_state_defines(visitor, mocker):
    e1 = make_edge(mocker, "e1", "x <= 5")
    e2 = make_edge(mocker, "e2", "x > 5")
    s1 = make_state(mocker, "Increment_x", "s1", in_edges=[e1])
    s2 = make_state(mocker, "End", "s2", in_edges=[e2])
    visitor._states = [s1, s2]
    output = visitor.generate_state_defines()
    assert "#define CWP_INCREMENT_X" in output
    assert "#define CWP_END" in output
    assert "#define CWP_NUM_STATES" in output
    assert "2" in output


def test_generate_update_cwp_state_contains_key_sections(visitor, mocker):
    src = make_state(mocker, "Start", "s0")
    mid = make_state(mocker, "Increment_x", "s1")
    end = make_state(mocker, "End", "s2")

    e_init = make_edge(mocker, "e0", "x == 0", source=None, dest=src)
    e_mid = make_edge(mocker, "e1", "x <= 5", source=src, dest=mid)
    e_end = make_edge(mocker, "e2", "x > 5", source=mid, dest=end)

    mid.in_edges = [e_mid]
    mid.out_edges = [e_end]
    end.in_edges = [e_end]
    end.out_edges = []
    src.in_edges = [e_init]
    src.out_edges = [e_mid]

    visitor._states = [src, mid, end]
    visitor._edges = {"e0": e_init, "e1": e_mid, "e2": e_end}

    output = visitor.generate_update_cwp_state(["int x"])

    assert (
        "static void update_cwp_state(int *cwp_state, bool cwp_reached[], int x)"
        in output
    )
    assert "bool e_UNKNOWN_to_Start" in output
    assert "bool e_Start_to_Increment_x" in output
    assert "bool e_Increment_x_to_End" in output
    assert "bool next_Increment_x" in output
    assert "bool next_End" in output
    assert "__CPROVER_assert(" in output
    assert "CWP P1: transition follows valid CWP edge" in output
    assert "*cwp_state             = new_state;" in output
    assert "cwp_reached[new_state] = true;" in output
