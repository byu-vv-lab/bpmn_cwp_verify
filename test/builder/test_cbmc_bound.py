# type: ignore
"""
Unit and integration tests for the CBMC bound computation helpers in cbmc_builder.py.

Covers:
  - _acyclic_depth:  sequential, XOR-split (max not min), back-edges, AND-fork correction
  - _find_matching_join: convergence cases and no-convergence
  - compute_bound: end-to-end with real BPMN fixtures (simple_example, face2face)
"""

from pathlib import Path

import pytest
from returns.pipeline import is_successful
from returns.unsafe import unsafe_perform_io

from bpmncwpverify.builder.cbmc_bound import (
    _acyclic_depth,
    _find_matching_join,
    compute_bound,
)
from bpmncwpverify.core.accessmethods import bpmnmethods
from bpmncwpverify.core.bpmn import (
    EndEvent,
    ExclusiveGatewayNode,
    ParallelGatewayNode,
    SequenceFlow,
    StartEvent,
    Task,
)
from bpmncwpverify.core.error import get_error_message
from bpmncwpverify.core.state import State
from bpmncwpverify.util.file import element_tree_from_string, read_file_as_string

# ── Graph builder helpers ──────────────────────────────────────────────────────

RESOURCES = Path(__file__).parent.parent / "resources"


def _task(id_: str) -> Task:
    return Task(id_, id_, "")


def _end(id_: str) -> EndEvent:
    return EndEvent(id_, id_, "", "")


def _start(id_: str) -> StartEvent:
    return StartEvent(id_, id_, "", "")


def _xor(id_: str) -> ExclusiveGatewayNode:
    return ExclusiveGatewayNode(id_, id_)


def _and_join(id_: str) -> ParallelGatewayNode:
    return ParallelGatewayNode(id_, id_, is_fork=False)


def _connect(source, target, flow_id: str | None = None) -> SequenceFlow:
    """Wire source → target with a SequenceFlow. Uses add_out_flow so
    ParallelGatewayNode.is_fork is set automatically on the second outflow."""
    flow = SequenceFlow(flow_id or f"f_{source.id}_{target.id}", "")
    flow.source_node = source
    flow.target_node = target
    source.add_out_flow(flow)
    target.add_in_flow(flow)
    return flow


def _load_bpmn(state_path: Path, bpmn_path: Path):
    state_str = unsafe_perform_io(read_file_as_string(str(state_path)).unwrap())
    bpmn_str = unsafe_perform_io(read_file_as_string(str(bpmn_path)).unwrap())
    state_result = State.from_str(state_str)
    assert is_successful(state_result), get_error_message(state_result.failure())
    bpmn_xml = unsafe_perform_io(element_tree_from_string(bpmn_str).unwrap())
    bpmn_result = bpmnmethods.from_xml(bpmn_xml, state_result.unwrap())
    assert is_successful(bpmn_result), get_error_message(bpmn_result.failure())
    return bpmn_result.unwrap()


# ── _acyclic_depth ─────────────────────────────────────────────────────────────


class TestAcyclicDepth:
    def test_end_event_returns_one(self):
        end = _end("e")
        assert _acyclic_depth(end, frozenset()) == 1

    def test_linear_chain(self):
        # start → task → end   depth = 3
        start, task, end = _start("s"), _task("t"), _end("e")
        _connect(start, task)
        _connect(task, end)
        assert _acyclic_depth(start, frozenset()) == 3

    def test_node_already_in_path_returns_minus_one(self):
        task = _task("t")
        assert _acyclic_depth(task, frozenset({"t"})) == -1

    def test_node_with_no_outflows_returns_minus_one(self):
        # a task with no outgoing flows and not an EndEvent
        task = _task("t")
        assert _acyclic_depth(task, frozenset()) == -1

    def test_back_edge_excluded(self):
        # xor → task (back-edge): task has already been visited
        # Only valid branch is the end event, so depth = 1.
        xor = _xor("xor")
        end = _end("e")
        task = _task("t")
        _connect(xor, end)
        _connect(xor, task)
        _connect(task, xor)  # back-edge (will be excluded via path)
        # Simulate: xor is reached after visiting task (task is already in path)
        assert _acyclic_depth(xor, frozenset({"t"})) == 2  # 1(xor) + 1(end)

    def test_xor_uses_max_not_min(self):
        # xor → end (depth 1)
        # xor → task → end2 (depth 2)
        # With MAX the xor depth is 1 + 2 = 3; with MIN it would be 1 + 1 = 2.
        xor = _xor("xor")
        end = _end("e1")
        task = _task("t")
        end2 = _end("e2")
        _connect(xor, end)
        _connect(xor, task)
        _connect(task, end2)
        assert _acyclic_depth(xor, frozenset()) == 3

    def test_and_fork_corrects_double_counted_suffix(self):
        # fork → b1 → join → end
        # fork → b2 → join
        # Actual steps: fork(1) b1(1) b2(1) join(1) end(1) = 5
        # Naive sum would give: 1 + (1+1+1) + (1+1+1) = 7
        fork = ParallelGatewayNode("fork", "fork")
        b1 = _task("b1")
        b2 = _task("b2")
        join = _and_join("join")
        end = _end("e")
        _connect(fork, b1)
        _connect(fork, b2)
        _connect(b1, join)
        _connect(b2, join)
        _connect(join, end)
        assert _acyclic_depth(fork, frozenset()) == 5

    def test_nested_and_forks(self):
        # outer_fork → ob1 → outer_join → end
        # outer_fork → inner_fork → ib1 → inner_join → outer_join
        #              inner_fork → ib2 → inner_join
        # Actual: outer_fork(1) ob1(1) inner_fork(1) ib1(1) ib2(1) inner_join(1) outer_join(1) end(1) = 8
        outer_fork = ParallelGatewayNode("of", "of")
        ob1 = _task("ob1")
        inner_fork = ParallelGatewayNode("if_", "if_")
        ib1 = _task("ib1")
        ib2 = _task("ib2")
        inner_join = _and_join("ij")
        outer_join = _and_join("oj")
        end = _end("e")
        _connect(outer_fork, ob1)
        _connect(outer_fork, inner_fork)
        _connect(inner_fork, ib1)
        _connect(inner_fork, ib2)
        _connect(ib1, inner_join)
        _connect(ib2, inner_join)
        _connect(inner_join, outer_join)
        _connect(ob1, outer_join)
        _connect(outer_join, end)
        assert _acyclic_depth(outer_fork, frozenset()) == 8


# ── _find_matching_join ────────────────────────────────────────────────────────


class TestFindMatchingJoin:
    def test_two_branches_converge_at_join(self):
        fork = ParallelGatewayNode("fork", "fork")
        b1 = _task("b1")
        b2 = _task("b2")
        join = _and_join("join")
        end = _end("e")
        _connect(fork, b1)
        _connect(fork, b2)
        _connect(b1, join)
        _connect(b2, join)
        _connect(join, end)
        result = _find_matching_join(fork, frozenset({"fork"}))
        assert result is not None
        assert result.id == "join"

    def test_no_convergence_returns_none(self):
        # fork → b1 → end1
        # fork → b2 → end2   (branches never meet)
        fork = ParallelGatewayNode("fork", "fork")
        b1 = _task("b1")
        b2 = _task("b2")
        _connect(fork, b1)
        _connect(fork, b2)
        _connect(b1, _end("e1"))
        _connect(b2, _end("e2"))
        result = _find_matching_join(fork, frozenset({"fork"}))
        assert result is None

    def test_single_outflow_returns_none(self):
        # A "fork" with only one outgoing flow is really sequential — no join needed.
        fork = ParallelGatewayNode("fork", "fork")
        task = _task("t")
        _connect(fork, task)
        result = _find_matching_join(fork, frozenset({"fork"}))
        assert result is None

    def test_join_blocked_by_path_returns_none(self):
        # The matching join is already in the acyclic path (back-edge scenario).
        fork = ParallelGatewayNode("fork", "fork")
        b1 = _task("b1")
        b2 = _task("b2")
        join = _and_join("join")
        _connect(fork, b1)
        _connect(fork, b2)
        _connect(b1, join)
        _connect(b2, join)
        # join is already in path — _find_matching_join should not return it
        result = _find_matching_join(fork, frozenset({"fork", "join"}))
        assert result is None


# ── compute_bound with real fixtures ─────────────────────────────────────────


class TestComputeBoundSimpleExample:
    @pytest.fixture(scope="class")
    def bpmn(self):
        return _load_bpmn(
            RESOURCES / "simple_example" / "state.txt",
            RESOURCES / "simple_example" / "simple_open.bpmn",
        )

    def test_bound_default_retries(self, bpmn):
        # acyclic depth 4 + cycle(len=2) × 2 retries = 8
        assert compute_bound(bpmn, max_retries=2) == 8

    def test_bound_scales_with_retries(self, bpmn):
        # acyclic 4 + cycle(2) × 4 = 12
        assert compute_bound(bpmn, max_retries=4) == 12

    def test_bound_minimum_is_acyclic_depth(self, bpmn):
        # With max_retries=0, only the acyclic skeleton contributes.
        assert compute_bound(bpmn, max_retries=0) == 4


class TestComputeBoundFace2Face:
    @pytest.fixture(scope="class")
    def bpmn(self):
        return _load_bpmn(
            RESOURCES / "face2face" / "state.txt",
            RESOURCES / "face2face" / "face2face_open.bpmn",
        )

    def test_bound_default_retries(self, bpmn):
        # acyclic 13 + loop total 12 = 25 (empirically verified minimum)
        assert compute_bound(bpmn, max_retries=2) == 25

    def test_bound_scales_with_retries(self, bpmn):
        # acyclic 13 + loop total (2+4) × 3 = 13 + 18 = 31
        assert compute_bound(bpmn, max_retries=3) == 31

    def test_bound_minimum_is_acyclic_depth(self, bpmn):
        assert compute_bound(bpmn, max_retries=0) == 13
