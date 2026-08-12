# type: ignore
import pytest
from returns.functions import not_
from returns.pipeline import is_successful
from returns.result import Success

from bpmncwpverify.builder.cwp_builder import CwpBuilder
from bpmncwpverify.core.cwp import Cwp, CwpEdge, CwpState
from bpmncwpverify.core.error import (
    CwpEdgeInvalidStateError,
    CwpMultStartStateError,
    CwpNoEndStatesError,
    CwpNoParentEdgeError,
    CwpNoStartStateError,
)


@pytest.fixture
def builder():
    return CwpBuilder()


def create_mock_state(mocker, state_id, out_edges=None, in_edges=None):
    state = mocker.MagicMock()
    state.id = state_id
    state.out_edges = out_edges if out_edges is not None else []
    state.in_edges = in_edges if in_edges is not None else []
    return state


def create_mock_edge(mocker, name, dest=None):
    edge = mocker.MagicMock()
    edge.name = name
    edge.dest = dest
    edge.is_leaf = False
    return edge


def test_gen_edge_name(builder):
    assert builder.gen_edge_name() == "EdgeA"
    assert builder.gen_edge_name() == "EdgeB"
    assert builder.gen_edge_name() == "EdgeC"


def test_with_edge_appends_pending(mocker, builder):
    mock_edge = mocker.MagicMock()

    builder.with_edge(mock_edge, "node1", "node2")

    assert builder._pending_edges == [(mock_edge, "node1", "node2")]


def test_with_edge_resolve(mocker, builder):
    source = create_mock_state(mocker, "node1")
    dest = create_mock_state(mocker, "node2")
    builder._cwp.states = {"node1": source, "node2": dest}

    mock_edge = mocker.MagicMock()
    mock_edge.id = "edge1"

    builder._with_edge(mock_edge, "node1", "node2")

    mock_edge.set_source.assert_called_once_with(source)
    mock_edge.set_dest.assert_called_once_with(dest)
    assert builder._cwp.edges[mock_edge.id] == mock_edge
    assert dest.in_edges == [mock_edge]
    assert source.out_edges == [mock_edge]


def test_with_edge_resolve_invalid_state(mocker, builder):
    builder._cwp.states = {"node1": create_mock_state(mocker, "node1")}
    mock_edge = mocker.MagicMock()
    mock_edge.id = "edge1"

    with pytest.raises(Exception) as exc_info:
        builder._with_edge(mock_edge, "node1", "missing_node")

    assert isinstance(exc_info.value.args[0], CwpEdgeInvalidStateError)


def test_check_expression_appends_pending(mocker, builder):
    expr_checker = mocker.MagicMock()
    state = mocker.MagicMock()

    builder.check_expression(expr_checker, "expression", "parent", state)

    assert builder._pending_expressions == [
        (expr_checker, "expression", "parent", state)
    ]


def test_check_expression_resolve(mocker, builder):
    mock_edge = mocker.MagicMock()
    builder._cwp.edges = {"parent": mock_edge}
    mock_feel = mocker.MagicMock()
    mock_feel.type_check.return_value = Success(None)

    mocker.patch.object(
        CwpEdge, "cleanup_expression", return_value="cleaned_expression"
    )
    mocker.patch.object(CwpEdge, "build_ast", return_value=mock_feel)

    state = mocker.MagicMock()
    mock_expr_checker = mocker.MagicMock()

    builder._check_expression(mock_expr_checker, "expression", "parent", state)

    mock_feel.type_check.assert_called_once_with(state)
    assert mock_edge.expression == mock_feel


def test_check_expression_resolve_no_parent(mocker, builder):
    builder._cwp.edges = {"edge": mocker.MagicMock()}

    with pytest.raises(Exception) as exc_info:
        builder._check_expression(mocker.Mock(), mocker.Mock(), "parent", mocker.Mock())

    assert isinstance(exc_info.value.args[0], CwpNoParentEdgeError)


def test_with_start_edge_appends_pending(mocker, builder):
    mock_edge = mocker.MagicMock()

    result = builder.with_start_edge(mock_edge)

    assert builder._pending_start_edge is mock_edge
    assert result is builder


def test_with_start_edge_resolve(mocker, builder):
    start_state = create_mock_state(mocker, "state1")
    builder._cwp.states = {"state1": start_state}
    builder._cwp.start_state = start_state

    mock_edge = mocker.MagicMock()
    mock_edge.id = "start_edge"

    builder._with_start_edge(mock_edge)

    mock_edge.set_dest.assert_called_once_with(start_state)
    assert builder._cwp.edges[mock_edge.id] == mock_edge
    assert start_state.in_edges == [mock_edge]


def test_find_start_state(mocker, builder):
    states = {
        "state1": mocker.MagicMock(
            spec=CwpState, in_edges=[], out_edges=["edge1"], init_state=False
        ),
        "state2": mocker.MagicMock(
            spec=CwpState, in_edges=["edge1"], out_edges=["edge2"], init_state=False
        ),
        "state3": mocker.MagicMock(
            spec=CwpState, in_edges=["edge2"], out_edges=[], init_state=False
        ),
    }
    builder._cwp.states = states

    builder._find_start_state()

    assert builder._cwp.start_state == states["state1"]
    assert states["state1"].init_state


def test_find_start_state_no_start(mocker, builder):
    states = {
        "state1": mocker.MagicMock(
            spec=CwpState, in_edges=["edge"], out_edges=["edge"]
        ),
    }
    builder._cwp.states = states

    with pytest.raises(Exception) as exc_info:
        builder._find_start_state()

    assert isinstance(exc_info.value.args[0], CwpNoStartStateError)


def test_find_start_state_multiple_starts(mocker, builder):
    states = {
        "state1": mocker.MagicMock(spec=CwpState, in_edges=[], out_edges=["e1"]),
        "state2": mocker.MagicMock(spec=CwpState, in_edges=[], out_edges=["e2"]),
    }
    builder._cwp.states = states

    with pytest.raises(Exception) as exc_info:
        builder._find_start_state()

    assert isinstance(exc_info.value.args[0], CwpMultStartStateError)


def test_build_success(mocker, builder):
    state1 = create_mock_state(mocker, "state1")
    state2 = create_mock_state(mocker, "state2")
    state3 = create_mock_state(mocker, "state3")

    mock_cwp = mocker.MagicMock(spec=Cwp)
    mock_cwp.states = {"state1": state1, "state2": state2, "state3": state3}
    builder._cwp = mock_cwp
    mock_cwp.accept = mocker.MagicMock()

    edge1 = create_mock_edge(mocker, "edge1")
    edge2 = create_mock_edge(mocker, "edge2")
    start_edge = create_mock_edge(mocker, "Init_Edge")

    builder._pending_edges = [
        (edge1, "state1", "state2"),
        (edge2, "state2", "state3"),
    ]
    builder._pending_start_edge = start_edge

    result = builder.build()

    assert isinstance(result, Success)
    assert result.unwrap() is builder._cwp
    assert builder._cwp.start_state == state1
    assert state1.init_state is True
    builder._cwp.accept.assert_called_once()


def test_build_no_start_edge(mocker, builder):
    state1 = create_mock_state(mocker, "state1")
    state2 = create_mock_state(mocker, "state2")
    builder._cwp.states = {"state1": state1, "state2": state2}

    edge1 = create_mock_edge(mocker, "edge1")
    builder._pending_edges = [(edge1, "state1", "state2")]
    # builder._pending_start_edge left as None

    result = builder.build()

    assert not_(is_successful)(result)
    assert isinstance(result.failure(), CwpNoStartStateError)


def test_build_no_end_states(mocker, builder):
    # state1 -> state2, state2 -> state2 (self-loop), so state2 is never a leaf
    state1 = create_mock_state(mocker, "state1")
    state2 = create_mock_state(mocker, "state2")

    mock_cwp = mocker.MagicMock(spec=Cwp)
    mock_cwp.states = {"state1": state1, "state2": state2}
    builder._cwp = mock_cwp
    mock_cwp.accept = mocker.MagicMock()
    builder._cwp.accept = mocker.MagicMock()

    edge1 = create_mock_edge(mocker, "edge1")
    self_loop = create_mock_edge(mocker, "self_loop")
    start_edge = create_mock_edge(mocker, "Init_Edge")

    builder._pending_edges = [
        (edge1, "state1", "state2"),
        (self_loop, "state2", "state2"),
    ]
    builder._pending_start_edge = start_edge

    result = builder.build()

    assert not_(is_successful)(result)
    assert isinstance(result.failure(), CwpNoEndStatesError)
