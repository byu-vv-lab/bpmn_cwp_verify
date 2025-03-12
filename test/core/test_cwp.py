# type: ignore
from xml.etree.ElementTree import Element, SubElement

from bpmncwpverify.core.error import (
    CwpMultStartStateError,
    CwpNoEndStatesError,
    CwpNoStartStateError,
    Error,
)
from returns.functions import not_
from bpmncwpverify.core.state import State
from returns.pipeline import is_successful
from bpmncwpverify.core.accessmethods.cwpmethods import from_xml
from bpmncwpverify.core.cwp import CwpEdge, CwpState
import pytest


def get_root_mx_root():
    root = Element("mxfile")

    diagram = SubElement(root, "diagram")

    mx_graph_model = SubElement(diagram, "mxGraphModel")

    mx_root = SubElement(mx_graph_model, "root")

    return root, mx_root


def build_state(code):
    state = State.from_str(code)
    assert is_successful(state)
    return state.unwrap()


def add_mx_cell(mx_root, **attributes):
    SubElement(mx_root, "mxCell", attrib=attributes)


def setup_cwp_and_assert(xml_root, state, success=True, failure_message=Error):
    cwp = from_xml(xml_root, state)
    if success:
        assert is_successful(cwp)
        return cwp.unwrap()
    else:
        assert not_(is_successful)(cwp)
        assert isinstance(cwp.failure(), failure_message)
    return cwp


def test_valid_cwp_end_start_events():
    state = build_state("var x: int = 0")
    root, mx_root = get_root_mx_root()

    add_mx_cell(mx_root, id="s1", value="Start", style="state", vertex="1")
    add_mx_cell(mx_root, id="s2", value="End", style="state", vertex="1")
    add_mx_cell(mx_root, id="e1", source="s1", target="s2", style="edge", edge="1")
    add_mx_cell(
        mx_root, id="expr1", value="x > 0", style="edgeLabel", parent="e1", vertex="1"
    )

    cwp = setup_cwp_and_assert(root, state)
    assert len(cwp.edges) == 1
    assert cwp.start_state.id == "s1"
    assert len(cwp.states) == 1


def test_invalid_cwp_missing_start_event():
    state = build_state("var x: int = 0")
    root, mx_root = get_root_mx_root()

    add_mx_cell(mx_root, id="s1", value="state", style="state", vertex="1")

    setup_cwp_and_assert(
        root, state, success=False, failure_message=CwpNoStartStateError
    )


def test_invalid_cwp_not_connected():
    state = build_state("var x: int = 0")
    root, mx_root = get_root_mx_root()

    # First disconnected component
    add_mx_cell(mx_root, id="s1", value="Start", style="state", vertex="1")
    add_mx_cell(mx_root, id="s2", value="End", style="state", vertex="1")
    add_mx_cell(mx_root, id="e1", source="s1", target="s2", style="edge", edge="1")
    add_mx_cell(
        mx_root, id="expr1", value="x > 0", style="edgeLabel", parent="e1", vertex="1"
    )

    # Second disconnected component
    add_mx_cell(mx_root, id="s3", value="Start", style="state", vertex="1")
    add_mx_cell(mx_root, id="s4", value="End", style="state", vertex="1")
    add_mx_cell(mx_root, id="e2", source="s3", target="s4", style="edge", edge="1")
    add_mx_cell(
        mx_root, id="expr1", value="x > 0", style="edgeLabel", parent="e2", vertex="1"
    )

    setup_cwp_and_assert(
        root,
        state,
        success=False,
        failure_message=CwpMultStartStateError,
    )


def test_invalid_cwp_no_end_state():
    state = build_state("var x: int = 0")
    root, mx_root = get_root_mx_root()

    add_mx_cell(mx_root, id="s1", value="Start", style="state", vertex="1")
    add_mx_cell(mx_root, id="s2", value="middle1", style="state", vertex="1")
    add_mx_cell(mx_root, id="s3", value="middle2", style="state", vertex="1")

    add_mx_cell(mx_root, id="e1", source="s1", target="s2", style="edge", edge="1")
    add_mx_cell(
        mx_root, id="expr1", value="x > 0", style="edgeLabel", parent="e1", vertex="1"
    )

    add_mx_cell(mx_root, id="e2", source="s2", target="s3", style="edge", edge="1")
    add_mx_cell(
        mx_root, id="expr2", value="x > 0", style="edgeLabel", parent="e1", vertex="1"
    )

    add_mx_cell(mx_root, id="e3", source="s3", target="s2", style="edge", edge="1")
    add_mx_cell(
        mx_root, id="expr3", value="x > 0", style="edgeLabel", parent="e1", vertex="1"
    )

    setup_cwp_and_assert(
        root,
        state,
        success=False,
        failure_message=CwpNoEndStatesError,
    )


@pytest.mark.parametrize(
    "input, expected",
    [
        (
            "&lt;div&gt;paymentOwner == buyerName &amp;amp;&amp;amp;&lt;/div&gt;&lt;div&gt;backpackOwner == sellerName&lt;br&gt;&lt;/div&gt;",
            "paymentOwner == buyerName && backpackOwner == sellerName",
        ),
        (
            "terms==noRetry || paymentOffered == noRetryPayment",
            "terms == noRetry || paymentOffered == noRetryPayment",
        ),
        (
            "terms == agreed &amp;amp;&amp;amp;&lt;br&gt;paymentOffered == paymentAmount",
            "terms == agreed && paymentOffered == paymentAmount",
        ),
        (
            "terms != pending ||&lt;br&gt;paymentOffered != pendingPayment",
            "terms != pending || paymentOffered != pendingPayment",
        ),
        ("x &amp;gt; 5", "x > 5"),
        ("x &amp;lt;= 5", "x <= 5"),
    ],
)
def test_cleanup_expression_with_good_examples(input, expected):
    actual = CwpEdge.cleanup_expression(input)
    assert actual == expected


def test_cwp_state_from_xml_with_no_id(mocker):
    mock_element = mocker.Mock()
    mock_element.get.side_effect = lambda x: {"id": None}.get(x)

    with pytest.raises(Exception) as exc_info:
        CwpState.from_xml(mock_element)

    assert exc_info.value.args[0] == "id not in cwp state"
