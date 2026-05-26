# type: ignore
"""
Unit tests for BpmnCbmcVisitor.

Follows the same mock-heavy, fixture-per-method pattern used in
test_bpmn_promela_visitor.py — no real BPMN parsing; node objects are
constructed via mocker.Mock(spec=...).
"""

import pytest

from bpmncwpverify.core.bpmn import (
    EndEvent,
    ExclusiveGatewayNode,
    IntermediateEvent,
    ParallelGatewayNode,
    SequenceFlow,
    StartEvent,
    Task,
)
from bpmncwpverify.core.error import CbmcUnsupportedElementError
from bpmncwpverify.visitors.bpmn_cbmc_visitor import BpmnCbmcVisitor


# ── helpers ───────────────────────────────────────────────────────────────────


def make_flow(mocker, source_id: str, target_id: str, fid: str, expression: str = ""):
    """Build a minimal SequenceFlow mock."""
    flow = mocker.Mock(spec=SequenceFlow)
    flow.id = fid
    flow.expression = expression
    src = mocker.Mock()
    src.id = source_id
    tgt = mocker.Mock()
    tgt.id = target_id
    flow.source_node = src
    flow.target_node = tgt
    return flow


@pytest.fixture
def visitor():
    return BpmnCbmcVisitor()


# ── name helpers ──────────────────────────────────────────────────────────────


def test_flow_place_name(mocker):
    flow = make_flow(mocker, "SRC", "TGT", "f1")
    assert BpmnCbmcVisitor._flow_place_name(flow) == "p_TGT_FROM_SRC"


def test_start_place_name(mocker):
    event = mocker.Mock(spec=StartEvent)
    event.id = "start_1"
    assert BpmnCbmcVisitor._start_place_name(event) == "p_start_1"


def test_transition_define_name_no_flow(mocker):
    node = mocker.Mock()
    node.id = "task_A"
    assert BpmnCbmcVisitor._transition_define_name(node, None) == "T_task_A"


def test_transition_define_name_with_flow(mocker):
    node = mocker.Mock()
    node.id = "gw_1"
    flow = mocker.Mock(spec=SequenceFlow)
    flow.id = "flow_X"
    assert BpmnCbmcVisitor._transition_define_name(node, flow) == "T_flow_X"


def test_enable_var_name_no_flow(mocker):
    node = mocker.Mock()
    node.id = "task_A"
    assert BpmnCbmcVisitor._enable_var_name(node, None) == "en_task_A"


def test_enable_var_name_with_flow(mocker):
    node = mocker.Mock()
    flow = mocker.Mock(spec=SequenceFlow)
    flow.id = "flow_X"
    assert BpmnCbmcVisitor._enable_var_name(node, flow) == "en_flow_X"


# ── enable expressions ────────────────────────────────────────────────────────


def test_enable_expr_start_event(visitor, mocker):
    event = mocker.Mock(spec=StartEvent)
    event.id = "ev_start"
    assert visitor._enable_expr(event, None) == "p_ev_start"


def test_enable_expr_task_single_in_flow(visitor, mocker):
    task = mocker.Mock(spec=Task)
    task.id = "task_1"
    src = mocker.Mock()
    src.id = "start_1"
    flow = mocker.Mock(spec=SequenceFlow)
    flow.source_node = src
    task.in_flows = [flow]
    assert visitor._enable_expr(task, None) == "p_task_1_FROM_start_1"


def test_enable_expr_task_multiple_in_flows(visitor, mocker):
    task = mocker.Mock(spec=Task)
    task.id = "task_1"
    src1 = mocker.Mock()
    src1.id = "gw_A"
    src2 = mocker.Mock()
    src2.id = "gw_B"
    f1 = mocker.Mock(spec=SequenceFlow)
    f1.source_node = src1
    f2 = mocker.Mock(spec=SequenceFlow)
    f2.source_node = src2
    task.in_flows = [f1, f2]
    assert visitor._enable_expr(task, None) == "p_task_1_FROM_gw_A || p_task_1_FROM_gw_B"


def test_enable_expr_xor_gateway_no_expression(visitor, mocker):
    gw = mocker.Mock(spec=ExclusiveGatewayNode)
    gw.id = "gw_1"
    src = mocker.Mock()
    src.id = "task_A"
    in_flow = mocker.Mock(spec=SequenceFlow)
    in_flow.source_node = src
    gw.in_flows = [in_flow]
    out_flow = mocker.Mock(spec=SequenceFlow)
    out_flow.expression = ""
    assert visitor._enable_expr(gw, out_flow) == "(p_gw_1_FROM_task_A)"


def test_enable_expr_xor_gateway_with_expression(visitor, mocker):
    gw = mocker.Mock(spec=ExclusiveGatewayNode)
    gw.id = "gw_1"
    src = mocker.Mock()
    src.id = "task_A"
    in_flow = mocker.Mock(spec=SequenceFlow)
    in_flow.source_node = src
    gw.in_flows = [in_flow]
    out_flow = mocker.Mock(spec=SequenceFlow)
    out_flow.expression = "x > 5"
    assert visitor._enable_expr(gw, out_flow) == "(p_gw_1_FROM_task_A) && (x > 5)"


# ── visitor callbacks ─────────────────────────────────────────────────────────


def test_visit_start_event_registers_place_and_transition(visitor, mocker):
    event = mocker.Mock(spec=StartEvent)
    event.id = "ev_start"
    result = visitor.visit_start_event(event)
    assert result is True
    assert "p_ev_start" in visitor._places
    assert visitor._places["p_ev_start"] is True
    assert len(visitor._transitions) == 1
    assert visitor._transitions[0] == (event, None)


def test_visit_start_event_deduplicates(visitor, mocker):
    event = mocker.Mock(spec=StartEvent)
    event.id = "ev_start"
    visitor.visit_start_event(event)
    result = visitor.visit_start_event(event)
    assert result is False
    assert len(visitor._transitions) == 1


def test_visit_task_registers_transition(visitor, mocker):
    task = mocker.Mock(spec=Task)
    task.id = "task_1"
    result = visitor.visit_task(task)
    assert result is True
    assert visitor._transitions[0] == (task, None)


def test_visit_task_deduplicates(visitor, mocker):
    task = mocker.Mock(spec=Task)
    task.id = "task_1"
    visitor.visit_task(task)
    result = visitor.visit_task(task)
    assert result is False
    assert len(visitor._transitions) == 1


def test_visit_exclusive_gateway_one_transition_per_out_flow(visitor, mocker):
    gw = mocker.Mock(spec=ExclusiveGatewayNode)
    gw.id = "gw_1"
    f1 = mocker.Mock(spec=SequenceFlow)
    f1.id = "flow_A"
    f2 = mocker.Mock(spec=SequenceFlow)
    f2.id = "flow_B"
    gw.out_flows = [f1, f2]
    result = visitor.visit_exclusive_gateway(gw)
    assert result is True
    assert len(visitor._transitions) == 2
    assert visitor._transitions[0] == (gw, f1)
    assert visitor._transitions[1] == (gw, f2)


def test_visit_end_event_registers_transition_and_id(visitor, mocker):
    event = mocker.Mock(spec=EndEvent)
    event.id = "ev_end"
    result = visitor.visit_end_event(event)
    assert result is True
    assert visitor._transitions[0] == (event, None)
    assert "ev_end" in visitor._end_event_ids


def test_visit_sequence_flow_registers_place(visitor, mocker):
    flow = make_flow(mocker, "SRC", "TGT", "f1")
    visitor.visit_sequence_flow(flow)
    assert "p_TGT_FROM_SRC" in visitor._places
    assert visitor._places["p_TGT_FROM_SRC"] is False


def test_visit_sequence_flow_does_not_overwrite_existing(visitor, mocker):
    flow = make_flow(mocker, "SRC", "TGT", "f1")
    visitor._places["p_TGT_FROM_SRC"] = True  # pre-set
    visitor.visit_sequence_flow(flow)
    assert visitor._places["p_TGT_FROM_SRC"] is True


def test_visit_parallel_gateway_sets_error(visitor, mocker):
    gw = mocker.Mock(spec=ParallelGatewayNode)
    gw.id = "gw_par"
    result = visitor.visit_parallel_gateway(gw)
    assert result is False
    assert isinstance(visitor.error, CbmcUnsupportedElementError)


def test_visit_intermediate_event_sets_error(visitor, mocker):
    event = mocker.Mock(spec=IntermediateEvent)
    event.id = "ev_int"
    result = visitor.visit_intermediate_event(event)
    assert result is False
    assert isinstance(visitor.error, CbmcUnsupportedElementError)


# ── transition body ───────────────────────────────────────────────────────────


def test_transition_body_start_event(visitor, mocker):
    event = mocker.Mock(spec=StartEvent)
    event.id = "ev_start"
    out_flow = make_flow(mocker, "ev_start", "task_1", "f_out")
    event.out_flows = [out_flow]
    lines = visitor._transition_body(event, None, [])
    assert "p_ev_start = false;" in lines[0]
    assert "p_task_1_FROM_ev_start = true;" in lines[1]


def test_transition_body_task_with_behavior(visitor, mocker):
    task = mocker.Mock(spec=Task)
    task.id = "task_1"
    task.behavior = "x = x + 1"
    in_flow = make_flow(mocker, "ev_start", "task_1", "f_in")
    out_flow = make_flow(mocker, "task_1", "gw_1", "f_out")
    task.in_flows = [in_flow]
    task.out_flows = [out_flow]
    lines = visitor._transition_body(task, None, ["x"])
    assert any("p_task_1_FROM_ev_start = false;" in l for l in lines)
    assert any("x = x + 1;" in l for l in lines)
    assert any("p_gw_1_FROM_task_1 = true;" in l for l in lines)
    assert any("update_cwp_state(&cwp_state, cwp_reached, x);" in l for l in lines)


def test_transition_body_task_without_behavior_no_update_call(visitor, mocker):
    task = mocker.Mock(spec=Task)
    task.id = "task_1"
    task.behavior = ""
    in_flow = make_flow(mocker, "ev_start", "task_1", "f_in")
    out_flow = make_flow(mocker, "task_1", "gw_1", "f_out")
    task.in_flows = [in_flow]
    task.out_flows = [out_flow]
    lines = visitor._transition_body(task, None, [])
    assert not any("update_cwp_state" in l for l in lines)


def test_transition_body_xor_gateway(visitor, mocker):
    gw = mocker.Mock(spec=ExclusiveGatewayNode)
    gw.id = "gw_1"
    in_flow = make_flow(mocker, "task_1", "gw_1", "f_in")
    out_flow = make_flow(mocker, "gw_1", "task_2", "f_out")
    gw.in_flows = [in_flow]
    lines = visitor._transition_body(gw, out_flow, [])
    assert any("p_gw_1_FROM_task_1 = false;" in l for l in lines)
    assert any("p_task_2_FROM_gw_1 = true;" in l for l in lines)


def test_transition_body_end_event(visitor, mocker):
    event = mocker.Mock(spec=EndEvent)
    event.id = "ev_end"
    in_flow = make_flow(mocker, "gw_1", "ev_end", "f_in")
    event.in_flows = [in_flow]
    lines = visitor._transition_body(event, None, [])
    assert any("p_ev_end_FROM_gw_1 = false;" in l for l in lines)
    assert any("ev_end_reached = true;" in l for l in lines)
    assert any("running = false;" in l for l in lines)


# ── code generation ───────────────────────────────────────────────────────────


def test_generate_transition_defines(visitor, mocker):
    task = mocker.Mock(spec=Task)
    task.id = "task_A"
    end = mocker.Mock(spec=EndEvent)
    end.id = "ev_end"
    visitor._transitions = [(task, None), (end, None)]
    output = visitor.generate_transition_defines()
    assert "#define T_task_A" in output
    assert "#define T_ev_end" in output


def test_num_transitions(visitor, mocker):
    task = mocker.Mock(spec=Task)
    task.id = "task_1"
    visitor.visit_task(task)
    assert visitor.num_transitions == 1


def test_compute_bound_is_transitions_times_four(visitor, mocker):
    task = mocker.Mock(spec=Task)
    task.id = "task_1"
    visitor._transitions = [(task, None)] * 3
    assert visitor.compute_bound() == 12
