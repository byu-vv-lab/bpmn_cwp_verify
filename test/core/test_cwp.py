# type: ignore
from xml.etree.ElementTree import Element, SubElement

import pytest
from returns.functions import not_
from returns.pipeline import is_successful

from bpmncwpverify.core.cwp import CwpEdge, CwpState
from bpmncwpverify.core.error import (
    CwpNoEndStatesError,
    CwpNoStartStateError,
    Error,
)
from bpmncwpverify.core.frontends.cwpXmlParser import CwpXmlParser
from bpmncwpverify.core.state import State


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
    cwp = CwpXmlParser.from_xml(xml_root, state)
    if success:
        assert is_successful(cwp)
        return cwp.unwrap()
    else:
        assert not_(is_successful)(cwp)
        assert isinstance(cwp.failure(), failure_message)
    return cwp


def test_valid_cwp_end_start_events():
    state = build_state("var x: int")
    root, mx_root = get_root_mx_root()

    add_mx_cell(mx_root, id="s1", value="Start", style="rounded=1;state", vertex="1")
    add_mx_cell(mx_root, id="s2", value="End", style="rounded=1;state", vertex="1")
    add_mx_cell(mx_root, id="e1", target="s1", style="edge", edge="1")
    add_mx_cell(mx_root, id="e2", source="s1", target="s2", style="edge", edge="2")
    add_mx_cell(
        mx_root, id="expr1", value="x = 0", style="edgeLabel", parent="e1", vertex="1"
    )
    add_mx_cell(
        mx_root, id="expr2", value="x > 0", style="edgeLabel", parent="e2", vertex="1"
    )

    cwp = setup_cwp_and_assert(root, state)
    assert len(cwp.edges) == 2
    assert "s1" in cwp.edges
    assert "e2" in cwp.edges
    assert cwp.start_state.id == "s1"
    assert len(cwp.states) == 2
    assert "s1" in cwp.states
    assert "s2" in cwp.states


def test_invalid_cwp_missing_start_event():
    state = build_state("var x: int")
    root, mx_root = get_root_mx_root()

    add_mx_cell(mx_root, id="s1", value="state", style="rounded=1;state", vertex="1")

    setup_cwp_and_assert(
        root, state, success=False, failure_message=CwpNoStartStateError
    )


def test_invalid_cwp_not_connected():
    state = build_state("var x: int")
    root, mx_root = get_root_mx_root()

    # First disconnected component
    add_mx_cell(mx_root, id="s1", value="Start", style="rounded=1;state", vertex="1")
    add_mx_cell(mx_root, id="s2", value="End", style="rounded=1;state", vertex="1")
    add_mx_cell(mx_root, id="e1", source="s1", target="s2", style="edge", edge="1")
    add_mx_cell(
        mx_root, id="expr1", value="x > 0", style="edgeLabel", parent="e1", vertex="1"
    )

    # Second disconnected component
    add_mx_cell(mx_root, id="s3", value="Start", style="rounded=1;state", vertex="1")
    add_mx_cell(mx_root, id="s4", value="End", style="rounded=1;state", vertex="1")
    add_mx_cell(mx_root, id="e2", source="s3", target="s4", style="edge", edge="1")
    add_mx_cell(
        mx_root, id="expr1", value="x > 0", style="edgeLabel", parent="e2", vertex="1"
    )

    setup_cwp_and_assert(
        root,
        state,
        success=False,
        failure_message=CwpNoStartStateError,
    )


def test_invalid_cwp_no_end_state():
    state = build_state("var x: int")
    root, mx_root = get_root_mx_root()

    add_mx_cell(mx_root, id="s1", value="Start", style="rounded=1;state", vertex="1")
    add_mx_cell(mx_root, id="s2", value="middle1", style="rounded=1;state", vertex="1")
    add_mx_cell(mx_root, id="s3", value="middle2", style="rounded=1;state", vertex="1")

    add_mx_cell(mx_root, id="e0", target="s1", style="edge", edge="1")
    add_mx_cell(
        mx_root, id="expr1", value="x = 0", style="edgeLabel", parent="e0", vertex="1"
    )

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
            "&lt;div&gt;paymentOwner = buyerName and backpackOwner = sellerName&lt;/div&gt;",
            "paymentOwner = buyerName and backpackOwner = sellerName",
        ),
        (
            "terms=noRetry or paymentOffered = noRetryPayment",
            "terms = noRetry or paymentOffered = noRetryPayment",
        ),
        (
            "terms = agreed  and &lt;br&gt;paymentOffered = paymentAmount",
            "terms = agreed and paymentOffered = paymentAmount",
        ),
        (
            "terms != pending or &lt;br&gt;paymentOffered != pendingPayment",
            "terms != pending or paymentOffered != pendingPayment",
        ),
        ("x &amp;gt; 5", "x > 5"),
        ("x &amp;lt;= 5", "x <= 5"),
        (
            "(search = on and blackBox = missing and risk = assessing&amp;nbsp;&lt;span style=&quot;background-color: light-dark(#ffffff, var(--ge-dark-color, #121212)); color: light-dark(rgb(0, 0, 0), rgb(255, 255, 255));&quot;&gt;and uuvComms = wait and conditions = changed)&lt;/span&gt;",
            "(search = on and blackBox = missing and risk = assessing and uuvComms = wait and conditions = changed)",
        ),
        (
            "&lt;div&gt;paymentOwner = buyerName and &lt;span style=&quot;color:red;&quot;&gt;status = paid&lt;/span&gt; and backpackOwner = sellerName &lt;span style=&quot;background:yellow;&quot;&gt;and shipped = true&lt;/span&gt;&lt;/div&gt;",
            "paymentOwner = buyerName and status = paid and backpackOwner = sellerName and shipped = true",
        ),
        (
            "terms !=NoRetry or bucketsOfMoney or not(suspicousSeller)",
            "terms != NoRetry or bucketsOfMoney or not(suspicousSeller)",
        ),
        (
            "user = loggedIn and status = active and ALERT and HIGHPRIORITY and role = admin",
            "user = loggedIn and status = active and ALERT and HIGHPRIORITY and role = admin",
        ),
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


def test_cwp_edge_from_xml_with_no_id(mocker):
    mock_element = mocker.Mock()
    mock_element.get.side_effect = lambda x: {"id": None}.get(x)

    with pytest.raises(Exception) as exc_info:
        CwpEdge.from_xml(mock_element, "test")

    assert exc_info.value.args[0] == "No ID for edge or no targetRef"
