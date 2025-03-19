# type: ignore
from bpmncwpverify.builder.cwp_builder import CwpBuilder
from bpmncwpverify.core.cwp import Cwp, CwpEdge, CwpState
from bpmncwpverify.core.error import (
    CwpNoParentEdgeError,
    CwpNoStartStateError,
)
from returns.result import Success
import pytest

from returns.pipeline import is_successful
from returns.functions import not_


@pytest.fixture
def builder():
    return CwpBuilder()


def create_mock_state(mocker, state_id, out_edges=None, in_edges=None):
    state = mocker.MagicMock()
    state.id = state_id
    state.out_edges = out_edges or []
    state.in_edges = in_edges or []
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


def test_check_expression(mocker):
    mock_expr_checker = mocker.MagicMock()
    mock_expr_checker.type_check.return_value = Success(None)

    state = mocker.MagicMock()

    builder = CwpBuilder()
    builder._cwp = Cwp()
    builder._cwp.edges = {"edge": mocker.MagicMock(), "parent": mocker.MagicMock()}

    expression = "expression"

    builder.check_expression(mock_expr_checker, expression, "parent", state)


def test_check_expression_no_parent(mocker):
    builder = CwpBuilder()
    builder._cwp = Cwp()
    builder._cwp.edges = {"edge": mocker.MagicMock()}

    with pytest.raises(Exception) as exc_info:
        builder.check_expression(
            mocker.Mock(), mocker.Mock(), mocker.Mock(), mocker.Mock()
        )

    assert isinstance(exc_info.value.args[0], CwpNoParentEdgeError)


def test_with_edge(mocker):
    builder = CwpBuilder()
    builder._cwp = Cwp()
    source = mocker.MagicMock()
    source.out_edges = []
    dest = mocker.MagicMock()
    dest.in_edges = []
    builder._cwp.states = {"node1": source, "node2": dest}

    mock_edge = mocker.MagicMock()
    mock_edge.id = "edge1"

    builder.with_edge(mock_edge, "node1", "node2")

    mock_edge.set_source.assert_called_once_with(source)
    mock_edge.set_dest.assert_called_once_with(dest)

    assert builder._cwp.edges[mock_edge.id] == mock_edge
    assert len(dest.in_edges) == 1
    assert len(source.out_edges) == 1


def test_build(mocker):
    states: dict[str, CwpState] = {
        "state1": mocker.MagicMock(spec=CwpState, in_edges=[], out_edges=["edge1"]),
        "state2": mocker.MagicMock(
            spec=CwpState, in_edges=["edge1"], out_edges=["edge2"]
        ),
        "state3": mocker.MagicMock(spec=CwpState, in_edges=["edge2"], out_edges=[]),
    }
    edges = {"edge1": mocker.MagicMock(), "edge2": mocker.MagicMock()}

    mock_cwp = mocker.MagicMock()
    mock_cwp.states = states

    obj = CwpBuilder()
    obj._cwp = mock_cwp
    obj._cwp.states = states
    obj._cwp.edges = edges
    mock_cwp.accept = mocker.MagicMock()

    result = obj.build()

    assert isinstance(result, Success)
    assert result.unwrap() == mock_cwp

    start_state = states["state1"]
    end_states = [states["state3"]]
    assert mock_cwp.start_state == start_state
    assert list(end_states) == [states["state3"]]

    mock_cwp.accept.assert_called_once()

    new_edge = CwpEdge(mocker.MagicMock(), mocker.MagicMock())
    states["state1"].in_edges = [new_edge]
    states["state3"].out_edges = [new_edge]

    result = obj.build()

    assert not_(is_successful)(result)
    assert isinstance(result.failure(), CwpNoStartStateError)
