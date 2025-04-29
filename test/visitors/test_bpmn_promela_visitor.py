from bpmncwpverify.core.bpmn import IntermediateEvent, ParallelGatewayNode, Task
import pytest
from bpmncwpverify.visitors.bpmn_promela_visitor import (
    PromelaGenVisitor,
    NL_NONE,
    NL_SINGLE,
    Context,
)
from bpmncwpverify.util.stringmanager import StringManager, IndentAction


@pytest.fixture
def string_manager_factory():
    def _factory():
        return StringManager()

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
    manager1: StringManager = string_manager_factory()
    manager2: StringManager = string_manager_factory()
    manager1.contents = []

    manager1.indent = 1

    manager1.write_str("hello", NL_NONE, IndentAction.NIL)

    assert manager1.contents == ["hello"]

    manager2.write_str("test string 1", NL_NONE, IndentAction.NIL)
    manager2.write_str("test string 2", NL_NONE, IndentAction.NIL)

    manager1.write_str(manager2, NL_NONE, IndentAction.NIL)

    assert manager1.contents == ["hello", "test string 1", "test string 2"]


def test_string_manager_write_str_with_tab(string_manager_factory):
    manager1: StringManager = string_manager_factory()
    manager2: StringManager = string_manager_factory()
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
    assert isinstance(promela_visitor.defs, StringManager)
    assert isinstance(promela_visitor.init_proc_contents, StringManager)
    assert isinstance(promela_visitor.promela, StringManager)
    assert repr(promela_visitor) == ""


def test_generate_location_label(promela_visitor, mocker):
    element = mocker.Mock(spec=Task)
    element.id = "TEST"
    ctx = mocker.Mock(spec=Context)
    ctx.element = element
    flow_or_message = mocker.Mock()
    flow_or_message.source_node.id = "SRC"

    ret_val = promela_visitor._generate_location_label(ctx, flow_or_message)

    assert ret_val == "TEST_FROM_SRC"

    ctx.task_end = True
    ret_val = promela_visitor._generate_location_label(ctx)

    assert ret_val == "TEST_END"

    element_no_spec = mocker.Mock()
    element_no_spec.id = "TEST"
    ctx.element = element_no_spec
    ctx.task_end = False

    ret_val = promela_visitor._generate_location_label(ctx)

    assert ret_val == "TEST"


def test_get_consume_locations(promela_visitor, mocker):
    node1 = mocker.Mock()
    node1.in_flows = []
    node1.in_msgs = []
    node1.id = "NODE1"

    node2 = mocker.Mock()
    node2.id = "NODE2"

    node3 = mocker.Mock()
    node3.id = "NODE3"

    ctx = mocker.Mock(spec=Context)
    ctx.element = node1
    ctx.task_end = False

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
    node1.id = "NODE1"

    node2 = mocker.Mock()
    node2.id = "NODE2"

    node3 = mocker.Mock()
    node3.id = "NODE3"

    ctx = mocker.Mock(spec=Context)
    ctx.element = node1
    ctx.task_end = False

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
    node1.id = "NODE1"

    node2 = mocker.Mock()
    node2.id = "NODE2"

    node3 = mocker.Mock()
    node3.id = "NODE3"

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
    ctx.task_end = False
    ctx.is_parallel = False

    guard = promela_visitor._build_guard(ctx)

    assert str(guard) == "(hasToken(NODE1_FROM_NODE2) || hasToken(NODE1_FROM_NODE3))"


def test_build_guard_with_parallel_gw(promela_visitor, mocker):
    node1 = mocker.Mock()
    node1.id = "NODE1"

    node2 = mocker.Mock()
    node2.id = "NODE2"

    node3 = mocker.Mock()
    node3.id = "NODE3"

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
    ctx.task_end = False
    ctx.is_parallel = True

    guard = promela_visitor._build_guard(ctx)

    assert str(guard) == "(hasToken(NODE1_FROM_NODE2) && hasToken(NODE1_FROM_NODE3))"


def test_build_atomic_block(promela_visitor, mocker):
    node1 = mocker.Mock()
    node1.id = "NODE1"

    node2 = mocker.Mock()
    node2.id = "NODE2"

    node3 = mocker.Mock()
    node3.id = "NODE3"

    node4 = mocker.Mock()
    node4.id = "NODE4"

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
    ctx.end_event = False
    ctx.task_end = False
    ctx.is_parallel = False
    ctx.has_option = False

    atomic_block = promela_visitor._build_atomic_block(ctx)

    expected_output = ":: atomic { ((hasToken(NODE1_FROM_NODE2) || hasToken(NODE1_FROM_NODE3))) ->\n\tNODE1_BehaviorModel()\n\td_step {\n\t\tconsumeToken(NODE1_FROM_NODE2)\n\t\tconsumeToken(NODE1_FROM_NODE3)\n\t\tputToken(NODE4_FROM_NODE1)\n\t}\n}\n"
    assert str(atomic_block) == expected_output


def test_gen_behavior_model(promela_visitor, mocker):
    node1 = mocker.Mock()
    node1.id = "TEST"

    ctx = mocker.Mock(spec=Context)
    ctx.element = node1
    ctx.behavior = ""

    promela_visitor._gen_behavior_model(ctx)
    assert (
        str(promela_visitor.behaviors)
        == "inline TEST_BehaviorModel() {\n\tupdateState()\n\tstateLogger()\n}\n\n"
    )


def test_gen_behavior_model_with_behavior(promela_visitor, mocker):
    node1 = mocker.Mock()
    node1.id = "TEST"

    ctx = mocker.Mock(spec=Context)
    ctx.element = node1
    ctx.behavior = (
        "\n\n\n\nif\n\n\n\n\t\t   :: true -> test\n\n :: true -> test2\n\nfi\n\n\n"
    )

    promela_visitor._gen_behavior_model(ctx)
    assert (
        str(promela_visitor.behaviors)
        == "inline TEST_BehaviorModel() {\n\tif\n\t\t:: true -> test\n\t\t:: true -> test2\n\tfi\n\tupdateState()\n\tstateLogger()\n}\n\n"
    )


def test_gen_var_defs(promela_visitor, mocker) -> None:
    mock_var_defs = mocker.Mock()
    promela_visitor.var_defs = mock_var_defs
    mock_get_consume_locations = mocker.patch.object(
        promela_visitor, "_get_consume_locations", return_value=["VAL1", "VAL2"]
    )
    node1 = mocker.Mock()
    node1.id = "TEST"

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


def test_build_expr_conditional(promela_visitor, mocker):
    mock_sm = mocker.patch("bpmncwpverify.visitors.bpmn_promela_visitor.StringManager")

    node1, node2, node3 = mocker.Mock(), mocker.Mock(), mocker.Mock()
    node1.id = "TEST1"
    node2.id = "TEST2"
    node3.id = "TEST3"

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
    ctx.task_end = False

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


def test_get_expressions(promela_visitor, mocker):
    node = mocker.Mock()

    ctx = mocker.Mock()
    ctx.element = node

    flow1 = mocker.Mock()
    flow1.expression = "TEST_EXPR1"
    flow2 = mocker.Mock()
    flow2.expression = "TEST_EXPR2"
    flow3 = mocker.Mock()
    flow3.expression = None

    node.out_flows = [flow1, flow2, flow3]

    result = promela_visitor._get_expressions(ctx)
    assert result == ["TEST_EXPR1", "TEST_EXPR2"]


def test_context_setters(mocker):
    task = mocker.Mock(spec=Task)
    parallel_gw = mocker.Mock(spec=ParallelGatewayNode)

    ctx = Context(task)

    with pytest.raises(AssertionError) as exc_info:
        ctx.is_parallel = True

    assert (
        exc_info.value.args[0]
        == "is_parallel can only be set if element is of type ParallelGatewayNode"
    )

    ctx = Context(parallel_gw)

    with pytest.raises(AssertionError) as exc_info:
        ctx.task_end = True

    assert (
        exc_info.value.args[0] == "task_end can only be set if element is of type Task"
    )

    ctx.is_parallel = True

    assert ctx.is_parallel


def test_visit_parallel_gateway(promela_visitor, mocker):
    mock_ctx = mocker.patch("bpmncwpverify.visitors.bpmn_promela_visitor.Context")
    mock_gen_var_defs = mocker.patch.object(PromelaGenVisitor, "_gen_var_defs")
    mock_build_atomic_block = mocker.patch.object(
        PromelaGenVisitor, "_build_atomic_block"
    )
    mock_gw = mocker.Mock(spec=ParallelGatewayNode)
    mock_gw.is_fork = False
    mock_ctx.return_value = mocker.Mock()

    promela_visitor.visit_parallel_gateway(mock_gw)

    mock_gen_var_defs.assert_called_once()
    mock_build_atomic_block.assert_called_once()


def test_visit_intermediate_event(promela_visitor, mocker):
    mock_ctx = mocker.patch("bpmncwpverify.visitors.bpmn_promela_visitor.Context")
    mock_gen_behavior_model = mocker.patch.object(
        PromelaGenVisitor, "_gen_behavior_model"
    )
    mock_gen_var_defs = mocker.patch.object(PromelaGenVisitor, "_gen_var_defs")
    mock_build_atomic_block = mocker.patch.object(
        PromelaGenVisitor, "_build_atomic_block"
    )
    mock_event = mocker.Mock(spec=IntermediateEvent)
    mock_ctx.return_value = mocker.Mock()

    promela_visitor.visit_intermediate_event(mock_event)

    mock_gen_behavior_model.assert_called_once()
    mock_gen_var_defs.assert_called_once()
    mock_build_atomic_block.assert_called_once()


def test_visit_task_with_behavior(promela_visitor, mocker):
    mock_gen_method = mocker.patch(
        "bpmncwpverify.visitors.bpmn_promela_visitor.PromelaGenVisitor._gen_behavior_model"
    )
    mocker.patch(
        "bpmncwpverify.visitors.bpmn_promela_visitor.PromelaGenVisitor._gen_var_defs"
    )
    mocker.patch(
        "bpmncwpverify.visitors.bpmn_promela_visitor.PromelaGenVisitor._build_atomic_block"
    )
    mock_context_class = mocker.patch(
        "bpmncwpverify.visitors.bpmn_promela_visitor.Context"
    )

    mock_context_object = mocker.Mock()
    mock_context_class.return_value = mock_context_object

    promela_visitor.visit_task(mocker.Mock())
    mock_gen_method.assert_called_once_with(mock_context_object)


def test_print_element_id(promela_visitor, mocker):
    sm = mocker.patch(
        "bpmncwpverify.visitors.bpmn_promela_visitor.StringManager.write_str"
    )
    mock_element = mocker.Mock(id="test_id")

    promela_visitor.print_element_id(mock_element)
    sm.assert_called_once_with('printf("ID: test_id")', 1)
