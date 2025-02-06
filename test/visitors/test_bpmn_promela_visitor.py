from bpmncwpverify.core.bpmn import Task
import pytest
from bpmncwpverify.visitors.bpmn_promela_visitor import (
    NL_DOUBLE,
    IndentAction,
    PromelaGenVisitor,
    NL_NONE,
    NL_SINGLE,
    Context,
)


@pytest.fixture
def string_manager_factory():
    def _factory():
        return PromelaGenVisitor.StringManager()

    return _factory


@pytest.fixture
def promela_visitor():
    return PromelaGenVisitor()


def test_string_manager_initial_state(string_manager_factory):
    manager1 = string_manager_factory()
    assert manager1.contents == []
    assert manager1.indent == NL_NONE


def test_string_manager_write_str(string_manager_factory):
    manager1 = string_manager_factory()
    manager1.write_str("test", NL_SINGLE, IndentAction.NIL)
    assert repr(manager1) == "test\n"


def test_string_manager_write_str_no_tab(string_manager_factory):
    manager1: PromelaGenVisitor.StringManager = string_manager_factory()
    manager2: PromelaGenVisitor.StringManager = string_manager_factory()
    manager1.contents = []

    manager1.indent = 1

    manager1.write_str("hello", NL_NONE, IndentAction.NIL)

    assert manager1.contents == ["hello"]

    manager2.write_str("test string 1", NL_NONE, IndentAction.NIL)
    manager2.write_str("test string 2", NL_NONE, IndentAction.NIL)

    manager1.write_str(manager2, NL_NONE, IndentAction.NIL)

    assert manager1.contents == ["hello", "test string 1", "test string 2"]


def test_string_manager_write_str_with_tab(string_manager_factory):
    manager1: PromelaGenVisitor.StringManager = string_manager_factory()
    manager2: PromelaGenVisitor.StringManager = string_manager_factory()
    manager1.contents = []
    manager1.indent = 1

    manager1.write_str("hello", NL_SINGLE, IndentAction.NIL)

    assert manager1.contents == ["hello\n"]

    manager2.write_str("test string 1", NL_SINGLE, IndentAction.NIL)
    manager2.write_str("test string 2", NL_SINGLE, IndentAction.NIL)

    manager1.write_str(manager2, NL_NONE, IndentAction.NIL)

    assert manager1.contents == ["hello\n", "\ttest string 1\n", "\ttest string 2\n"]


def test_string_manager_indent_increment(string_manager_factory):
    manager = string_manager_factory()
    manager.write_str("start", NL_SINGLE, IndentAction.INC)
    manager.write_str("indented", NL_SINGLE, IndentAction.NIL)
    assert repr(manager) == "start\n\tindented\n"


def test_string_manager_indent_decrement(string_manager_factory):
    manager = string_manager_factory()
    manager.indent = 1
    manager.write_str("start", NL_SINGLE, IndentAction.DEC)
    manager.write_str("indented", NL_SINGLE, IndentAction.NIL)
    assert repr(manager) == "start\nindented\n"


def test_string_manager_multiple_calls(string_manager_factory):
    manager = string_manager_factory()
    manager.indent = 1
    manager.write_str("line1", NL_SINGLE, IndentAction.INC)
    manager.write_str("line2", NL_SINGLE, IndentAction.INC)
    manager.write_str("line3", NL_SINGLE, IndentAction.NIL)
    manager.write_str("line4", NL_SINGLE, IndentAction.DEC)

    expected_output = "line1\n\t\tline2\n\t\t\tline3\n\t\tline4\n"
    assert repr(manager) == expected_output


def test_string_manager_needs_tab_logic(string_manager_factory):
    manager = string_manager_factory()
    manager.write_str("first", NL_NONE, IndentAction.NIL)
    manager.write_str("second", NL_SINGLE, IndentAction.NIL)
    manager.write_str("third", NL_SINGLE, IndentAction.NIL)
    manager.write_str("fourth", NL_NONE, IndentAction.NIL)

    expected_output = "firstsecond\nthird\nfourth"
    assert repr(manager) == expected_output


def test_string_manager_indent(string_manager_factory):
    manager1 = string_manager_factory()
    manager1._inc_indent()
    assert manager1.indent == NL_SINGLE

    manager1._dec_indent()
    assert manager1.indent == NL_NONE


def test_string_manager_assertion_error_on_negative_indent(string_manager_factory):
    manager1 = string_manager_factory()
    with pytest.raises(AssertionError):
        manager1._dec_indent()


############################
# PromelaGenVisitor tests
############################


def test_promela_gen_visitor_initial_state(promela_visitor):
    assert isinstance(promela_visitor.defs, PromelaGenVisitor.StringManager)
    assert isinstance(
        promela_visitor.init_proc_contents, PromelaGenVisitor.StringManager
    )
    assert isinstance(promela_visitor.promela, PromelaGenVisitor.StringManager)
    assert repr(promela_visitor) == ""


def test_generate_location_label(promela_visitor, mocker):
    element = mocker.Mock(spec=Task)
    element.name = "TEST"
    ctx = mocker.Mock(spec=Context)
    ctx.element = element
    flow_or_message = mocker.Mock()
    flow_or_message.source_node.name = "SRC"

    ret_val = promela_visitor._generate_location_label(ctx, flow_or_message)

    assert ret_val == "TEST_FROM_SRC"

    ret_val = promela_visitor._generate_location_label(ctx)

    assert ret_val == "TEST_END"

    element_no_spec = mocker.Mock()
    element_no_spec.name = "TEST"
    ctx.element = element_no_spec

    ret_val = promela_visitor._generate_location_label(ctx)

    assert ret_val == "TEST"


def test_get_consume_locations(promela_visitor, mocker):
    node1 = mocker.Mock()
    node1.in_flows = []
    node1.in_msgs = []
    node1.name = "NODE1"

    node2 = mocker.Mock()
    node2.name = "NODE2"

    node3 = mocker.Mock()
    node3.name = "NODE3"

    ctx = mocker.Mock(spec=Context)
    ctx.element = node1

    assert promela_visitor._get_consume_locations(ctx) == ["NODE1"]

    flow1 = mocker.Mock()
    flow1.source_node = node1

    flow2 = mocker.Mock()
    flow2.source_node = node3

    node2.in_flows = [flow1]
    node2.in_msgs = [flow2]
    ctx.element = node2

    assert promela_visitor._get_consume_locations(ctx) == [
        "NODE2_FROM_NODE1",
        "NODE2_FROM_NODE3",
    ]


def test_get_put_locations(promela_visitor, mocker):
    node1 = mocker.Mock()
    node1.out_flows = []
    node1.out_msgs = []
    node1.name = "NODE1"

    node2 = mocker.Mock()
    node2.name = "NODE2"

    node3 = mocker.Mock()
    node3.name = "NODE3"

    ctx = mocker.Mock(spec=Context)
    ctx.element = node1

    assert promela_visitor._get_put_locations(ctx) == []

    flow1 = mocker.Mock()
    flow1.source_node = node1
    flow1.target_node = node2

    flow2 = mocker.Mock()
    flow2.source_node = node1
    flow2.target_node = node3

    node1.out_flows = [flow1]
    node1.out_msgs = [flow2]

    assert promela_visitor._get_put_locations(ctx) == [
        "NODE2_FROM_NODE1",
        "NODE3_FROM_NODE1",
    ]


def test_build_guard(promela_visitor, mocker):
    node1 = mocker.Mock()
    node1.name = "NODE1"

    node2 = mocker.Mock()
    node2.name = "NODE2"

    node3 = mocker.Mock()
    node3.name = "NODE3"

    flow1 = mocker.Mock()
    flow1.source_node = node2
    flow1.target_node = node1

    flow2 = mocker.Mock()
    flow2.source_node = node3
    flow2.target_node = node1

    node1.in_flows = [flow1, flow2]
    node1.in_msgs = []

    ctx = mocker.Mock(spec=Context)
    ctx.element = node1

    guard = promela_visitor._build_guard(ctx)

    assert str(guard) == "(hasToken(NODE1_FROM_NODE2) || hasToken(NODE1_FROM_NODE3))"


def test_build_atomic_block(promela_visitor, mocker):
    node1 = mocker.Mock()
    node1.name = "NODE1"

    node2 = mocker.Mock()
    node2.name = "NODE2"

    node3 = mocker.Mock()
    node3.name = "NODE3"

    node4 = mocker.Mock()
    node4.name = "NODE4"

    flow1 = mocker.Mock()
    flow1.source_node = node2
    flow1.target_node = node1

    flow2 = mocker.Mock()
    flow2.source_node = node3
    flow2.target_node = node1

    flow3 = mocker.Mock()
    flow3.source_node = node1
    flow3.target_node = node4

    node1.in_flows = [flow1, flow2]
    node1.in_msgs = []

    node1.out_flows = [flow3]
    node1.out_msgs = []

    ctx = mocker.Mock(spec=Context)
    ctx.element = node1

    atomic_block = promela_visitor._build_atomic_block(ctx)

    expected_output = ":: atomic { ((hasToken(NODE1_FROM_NODE2) || hasToken(NODE1_FROM_NODE3))) ->\n\tNODE1_BehaviorModel()\n\td_step {\n\t\tconsumeToken(NODE1_FROM_NODE2)\n\t\tconsumeToken(NODE1_FROM_NODE3)\n\t\tputToken(NODE4_FROM_NODE1)\n\t}\n}\n"
    assert str(atomic_block) == expected_output


def test_gen_behavior_model(promela_visitor, mocker):
    node1 = mocker.Mock()
    node1.name = "TEST"

    ctx = mocker.Mock(spec=Context)
    ctx.element = node1

    promela_visitor._gen_behavior_model(ctx)
    assert (
        str(promela_visitor.behaviors) == "inline TEST_BehaviorModel(){\n\tskip\n}\n\n"
    )


def test_gen_var_defs(promela_visitor, mocker) -> None:
    mock_var_defs = mocker.Mock()
    promela_visitor.var_defs = mock_var_defs
    mock_get_consume_locations = mocker.patch.object(
        promela_visitor, "_get_consume_locations", return_value=["VAL1", "VAL2"]
    )
    node1 = mocker.Mock()
    node1.name = "TEST"

    ctx = mocker.Mock(spec=Context)
    ctx.element = node1

    promela_visitor._gen_var_defs(ctx)

    mock_get_consume_locations.assert_called_once_with(ctx)

    mock_var_defs.write_str.assert_has_calls(
        [
            mocker.call("bit VAL1 = 0", 1),
            mocker.call("bit VAL2 = 0", 1),
        ],
        any_order=False,
    )


def test_gen_excl_gw_has_option(promela_visitor, mocker):
    mock_var_defs = mocker.Mock()
    promela_visitor.defs = mock_var_defs

    gw = mocker.Mock()
    gw.name = "TEST"

    flow1 = mocker.Mock()
    flow1.expression = "EXPR1"

    flow2 = mocker.Mock()
    flow2.expression = "EXPR2"

    gw.out_flows = [flow1, flow2]

    ctx = mocker.Mock(spec=Context)
    ctx.element = gw

    promela_visitor._gen_excl_gw_has_option(ctx)

    mock_var_defs.write_str.assert_has_calls(
        [
            mocker.call("#define TEST_hasOption \\", NL_SINGLE),
            mocker.call("( \\", NL_SINGLE, IndentAction.INC),
            mocker.call("EXPR1 || \\", NL_SINGLE),
            mocker.call("EXPR2 \\", NL_SINGLE),
            mocker.call(")", NL_DOUBLE, IndentAction.DEC),
        ]
    )


def test_build_expr_conditional(promela_visitor, mocker):
    mock_sm = mocker.patch(
        "bpmncwpverify.visitors.bpmn_promela_visitor.PromelaGenVisitor.StringManager"
    )

    node1, node2, node3 = mocker.Mock(), mocker.Mock(), mocker.Mock()
    node1.name = "TEST1"
    node2.name = "TEST2"
    node3.name = "TEST3"

    flow1, flow2 = mocker.Mock(), mocker.Mock()
    flow1.source_node = node1
    flow1.target_node = node2
    flow1.expression = "EXPR1"

    flow2.source_node = node1
    flow2.target_node = node3
    flow2.expression = "EXPR2"

    node1.out_flows = [flow1, flow2]
    node1.out_msgs = []

    ctx = mocker.Mock(spec=Context)
    ctx.element = node1

    mock_write_str = mocker.Mock()
    mock_sm.return_value = mocker.Mock()
    mock_sm.return_value.write_str = mock_write_str

    promela_visitor._build_expr_conditional(ctx)
    mock_write_str.assert_has_calls(
        [
            mocker.call("if", NL_SINGLE, IndentAction.INC),
            mocker.call(":: EXPR1 -> putToken(TEST2_FROM_TEST1)", NL_SINGLE),
            mocker.call(":: EXPR2 -> putToken(TEST3_FROM_TEST1)", NL_SINGLE),
            mocker.call(":: atomic{else -> assert false}", NL_SINGLE),
            mocker.call("fi", NL_SINGLE, IndentAction.DEC),
        ]
    )
