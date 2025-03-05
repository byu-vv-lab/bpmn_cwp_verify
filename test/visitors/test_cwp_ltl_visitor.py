# type: ignore
from returns.pipeline import is_successful

from bpmncwpverify.visitors.cwp_ltl_visitor import CwpLtlVisitor
from bpmncwpverify.core.cwp import Cwp
from bpmncwpverify.core.state import (
    AllowedValueDecl,
    StateBuilder,
    ConstDecl,
    EnumDecl,
    VarDecl,
)
import pytest


def test_write_init_states(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")

    state = mocker.MagicMock()
    instance = CwpLtlVisitor(state)

    instance.cwp = Cwp()
    instance.cwp.states = {
        "state1": type("", (), {"name": "init_state1"}),
        "state2": type("", (), {"name": "normal_state2"}),
    }

    instance.write_init_states()

    expected_calls = [
        mocker.call("\n\n//**********STATE VARIABLE DECLARATION************//"),
        mocker.call("bit init_state1 = 1"),
        mocker.call("bit normal_state2 = 0"),
    ]

    mock_write.assert_has_calls(expected_calls)


def test_cwp_write_exists_properties(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")

    state = mocker.MagicMock()
    state.name = "TestState"

    state = mocker.MagicMock()
    visitor = CwpLtlVisitor(state)
    visitor.property_list = []

    visitor.write_exists_property(state)

    assert "{}Exists".format(state.name) in visitor.property_list

    expected_call = mocker.call(
        "ltl TestStateExists {(fair implies (always (! TestState)))}"
    )

    mock_write.assert_has_calls([expected_call])


def test_cwp_mutex_property(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    state = mocker.MagicMock()
    state.name = "TestState"

    dummy_cwp = type("DummyCwp", (), {})()
    dummy_cwp.states = {
        "TestState": state,
        "OtherState1": mocker.MagicMock(name="OtherState1"),
        "OtherState2": mocker.MagicMock(name="OtherState2"),
        "OtherState3": mocker.MagicMock(name="OtherState3"),
    }
    dummy_cwp.states["OtherState1"].name = "OtherState1"
    dummy_cwp.states["OtherState2"].name = "OtherState2"
    dummy_cwp.states["OtherState3"].name = "OtherState3"

    state = mocker.MagicMock()
    visitor = CwpLtlVisitor(state)
    visitor.property_list = []
    visitor.cwp = dummy_cwp
    visitor.tab = 0

    visitor.write_mutex_property(state)

    assert "{}Mutex".format(state.name) in visitor.property_list

    expected_calls = [
        mocker.call("ltl TestStateMutex {"),
        mocker.call("("),
        mocker.call("always ("),
        mocker.call("TestState implies ("),
        mocker.call("TestState"),
        mocker.call(
            "&& (! OtherState1)\n\t\t\t\t&& (! OtherState2)\n\t\t\t\t&& (! OtherState3)"
        ),
        mocker.call(")"),
        mocker.call(")"),
        mocker.call(")"),
        mocker.call("}"),
    ]
    mock_write.assert_has_calls(expected_calls)

    assert visitor.tab == 0


def test_cwp_write_edges_property(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")

    state = mocker.MagicMock()
    state.name = "TestState"

    dest_state1 = mocker.MagicMock()
    dest_state1.name = "DestState1"
    dest_state2 = mocker.MagicMock()
    dest_state2.name = "DestState2"
    dest_state3 = mocker.MagicMock()
    dest_state3.name = "DestState3"

    state.out_edges = [
        mocker.MagicMock(dest=dest_state1),
        mocker.MagicMock(dest=dest_state2),
        mocker.MagicMock(dest=dest_state3),
    ]

    state = mocker.MagicMock()
    visitor = CwpLtlVisitor(state)
    visitor.property_list = []
    visitor.tab = 0

    visitor.write_edges_property(state)

    assert "{}Edges".format(state.name) in visitor.property_list

    expected_calls = [
        mocker.call("ltl TestStateEdges {"),
        mocker.call("("),
        mocker.call("fair implies ("),
        mocker.call("always ("),
        mocker.call("TestState implies ("),
        mocker.call("TestState until ("),
        mocker.call("DestState1\n\t\t\t\t\t\t|| DestState2\n\t\t\t\t\t\t|| DestState3"),
        mocker.call(")"),
        mocker.call(")"),
        mocker.call(")"),
        mocker.call(")"),
        mocker.call(")"),
        mocker.call("}"),
    ]

    mock_write.assert_has_calls(expected_calls)

    assert visitor.tab == 0


def test_cwp_write_state_variables(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    state_result = (
        StateBuilder()
        .with_const_decl(ConstDecl("CONST_A", "int", AllowedValueDecl("10")))
        .with_const_decl(ConstDecl("CONST_B", "int", AllowedValueDecl("20")))
        .with_enum_type_decl(
            EnumDecl(
                "EnumType",
                {
                    AllowedValueDecl("Value1"),
                    AllowedValueDecl("Value2"),
                    AllowedValueDecl("Value3"),
                },
            )
        )
        .with_var_decl(VarDecl("var1", "int", AllowedValueDecl("42"), list()))
        .with_var_decl(
            VarDecl("var2", "int", AllowedValueDecl("42"), [AllowedValueDecl("42")])
        )
        .build()
    )
    assert is_successful(state_result)
    state = state_result.unwrap()

    visitor = CwpLtlVisitor(state)

    visitor.write_state_variables()

    expected_calls = [
        mocker.call("\n\n//**********VARIABLE DECLARATION************//\n"),
        mocker.call("#define CONST_A 10"),
        mocker.call("\n"),
        mocker.call("#define CONST_B 20"),
        mocker.call("\n"),
        mocker.call("\n"),
        mocker.call("mytpe = {Value1 Value2 Value3}"),
        mocker.call("\n"),
        mocker.call("\n"),
        mocker.call("int var1 = 42"),
        mocker.call("\n"),
        mocker.call("int var2 = 42"),
        mocker.call("\n"),
        mocker.call("\n"),
    ]
    mock_write.assert_has_calls(expected_calls, any_order=False)


def test_cwp_write_variable_range_invariants(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    state_result = (
        StateBuilder()
        .with_enum_type_decl(
            EnumDecl(
                "TestEnum1",
                [
                    AllowedValueDecl("TestEnum1_1"),
                    AllowedValueDecl("TestEnum1_2"),
                    AllowedValueDecl("TestEnum1_3"),
                ],
            )
        )
        .with_enum_type_decl(
            EnumDecl(
                "TestEnum2",
                [
                    AllowedValueDecl("TestEnum2_1"),
                    AllowedValueDecl("TestEnum2_2"),
                    AllowedValueDecl("TestEnum2_3"),
                ],
            )
        )
        .build()
    )
    assert is_successful(state_result)
    state = state_result.unwrap()

    visitor = CwpLtlVisitor(state)
    visitor.state_info = []

    visitor.write_variable_range_invariants()

    assert visitor.state_info == [
        "\n\n//**********Variable Range Invariants************//"
    ]

    expected_calls = [
        mocker.call(
            "#define TestEnum1Invariant ((TestEnum1 == TestEnum1_1) || (TestEnum1 == TestEnum1_2) || (TestEnum1 == TestEnum1_3))"
        ),
        mocker.call(
            "#define TestEnum2Invariant ((TestEnum2 == TestEnum2_1) || (TestEnum2 == TestEnum2_2) || (TestEnum2 == TestEnum2_3))"
        ),
    ]

    mock_write.assert_has_calls(expected_calls)


def test_cwp_write_edge_definitions(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    mock_cwp = mocker.MagicMock()
    mock_cwp.edges = {
        "edge1": mocker.MagicMock(),
        "edge2": mocker.MagicMock(),
        "edge3": mocker.MagicMock(),
    }

    mock_cwp.edges["edge1"].name = "edge1"
    mock_cwp.edges["edge2"].name = "edge2"
    mock_cwp.edges["edge3"].name = "edge3"

    instance = CwpLtlVisitor(mocker.MagicMock())
    instance.cwp = mock_cwp

    instance.write_edge_definitions()

    expected_calls = [
        mocker.call("\n\n//**********EDGE DECLARATION************//"),
        mocker.call("bit edge1 = 0"),
        mocker.call("bit edge2 = 0"),
        mocker.call("bit edge3 = 0"),
    ]

    mock_write.assert_has_calls(expected_calls)


def test_cwp_write_variable_range_assertions(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    state_result = (
        StateBuilder()
        .with_var_decl(VarDecl("var1", "int", AllowedValueDecl("0"), []))
        .with_var_decl(VarDecl("var2", "int", AllowedValueDecl("0"), []))
        .with_var_decl(VarDecl("var3", "int", AllowedValueDecl("0"), []))
        .build()
    )
    assert is_successful(state_result)
    state = state_result.unwrap()

    visitor = CwpLtlVisitor(state)

    visitor.write_variable_range_assertions()

    expected_calls = [
        mocker.call("assert(var1Invariant)"),
        mocker.call("assert(var2Invariant)"),
        mocker.call("assert(var3Invariant)"),
    ]

    mock_write.assert_has_calls(expected_calls, any_order=False)


def test_cwp_write_refresh_edges(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    cwp = mocker.MagicMock()
    cwp.edges = {"edge1": mocker.MagicMock(), "edge2": mocker.MagicMock()}
    cwp.edges["edge1"].name = "Edge1"
    cwp.edges["edge1"].expression = "expression1"
    cwp.edges["edge2"].name = "Edge2"
    cwp.edges["edge2"].expression = "expression2"

    visitor = CwpLtlVisitor(mocker.MagicMock())
    visitor.cwp = cwp
    visitor.tab = 0

    visitor.write_refresh_edges()

    expected_calls = [
        mocker.call("if"),
        mocker.call(":: (expression1) -> "),
        mocker.call("Edge1 = 1"),
        mocker.call(":: else -> "),
        mocker.call("Edge1 = 0"),
        mocker.call("fi"),
        mocker.call("if"),
        mocker.call(":: (expression2) -> "),
        mocker.call("Edge2 = 1"),
        mocker.call(":: else -> "),
        mocker.call("Edge2 = 0"),
        mocker.call("fi"),
    ]

    mock_write.assert_has_calls(expected_calls, any_order=False)

    assert visitor.tab == 0


def test_cwp_write_refresh_states(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    in_edge1 = mocker.MagicMock()
    in_edge1.name = "InEdge1"
    in_edge2 = mocker.MagicMock()
    in_edge2.name = "InEdge2"
    out_edge1 = mocker.MagicMock()
    out_edge1.name = "OutEdge1"
    out_edge2 = mocker.MagicMock()
    out_edge2.name = "OutEdge2"

    cwp = mocker.MagicMock
    cwp.states = {"state1": mocker.MagicMock(), "state2": mocker.MagicMock()}
    cwp.states["state1"].name = "State1"
    cwp.states["state1"].in_edges = [in_edge1, in_edge2]
    cwp.states["state1"].out_edges = [out_edge1, out_edge2]

    cwp.states["state2"].name = "State2"
    cwp.states["state2"].in_edges = []
    cwp.states["state2"].out_edges = [out_edge1]

    visitor = CwpLtlVisitor(mocker.MagicMock())
    visitor.cwp = cwp
    visitor.tab = 0

    visitor.write_refresh_states()

    expected_calls = [
        mocker.call("State1 = "),
        mocker.call("("),
        mocker.call("(InEdge1 && InEdge2)"),
        mocker.call("&&"),
        mocker.call("(! (OutEdge1 || OutEdge2))"),
        mocker.call(")"),
        mocker.call("State2 = "),
        mocker.call("("),
        mocker.call("(! (OutEdge1))"),
        mocker.call(")"),
    ]

    mock_write.assert_has_calls(expected_calls, any_order=False)

    assert visitor.tab == 0


def test_cwp_write_ina_state_property(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    cwp = mocker.MagicMock()
    cwp.states = {
        "state1": mocker.MagicMock(),
        "state2": mocker.MagicMock(),
        "state3": mocker.MagicMock(),
    }
    cwp.states["state1"].name = "State1"
    cwp.states["state2"].name = "State2"
    cwp.states["state3"].name = "State3"

    visitor = CwpLtlVisitor(mocker.MagicMock())
    visitor.cwp = cwp
    visitor.property_list = []

    visitor.write_ina_state_property()

    assert "alwaysInAState" in visitor.property_list

    expected_calls = [
        mocker.call("#define inAState State1 \\\n || State2 \\\n || State3"),
        mocker.call("ltl alwaysInAState {(always (inAState))}"),
    ]

    mock_write.assert_has_calls(expected_calls, any_order=False)


def test_cwp_write_fair_property_debug_true(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    cwp = mocker.MagicMock()
    cwp.end_states = [mocker.MagicMock(), mocker.MagicMock()]
    cwp.end_states[0].name = "EndState1"
    cwp.end_states[1].name = "EndState2"

    visitor = CwpLtlVisitor(mocker.MagicMock())
    visitor.cwp = cwp
    visitor.property_list = []
    visitor.debug = True

    visitor.write_fair_property()

    assert "fairPathExists" in visitor.property_list

    expected_calls = [
        mocker.call("#define fair (true)"),
        mocker.call("ltl fairPathExists {(always (! fair))}"),
    ]

    mock_write.assert_has_calls(expected_calls, any_order=False)


def test_cwp_write_fair_property_debug_false(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    cwp = mocker.MagicMock()
    cwp.end_states = [mocker.MagicMock(), mocker.MagicMock()]
    cwp.end_states[0].name = "EndState1"
    cwp.end_states[1].name = "EndState2"

    visitor = CwpLtlVisitor(mocker.MagicMock())
    visitor.cwp = cwp
    visitor.property_list = []
    visitor.debug = False

    visitor.write_fair_property()

    assert "fairPathExists" in visitor.property_list

    expected_calls = [
        mocker.call("#define fair (eventually (EndState1 || EndState2))"),
        mocker.call("ltl fairPathExists {(always (! fair))}"),
    ]

    mock_write.assert_has_calls(expected_calls, any_order=False)


def test_cwp_write_log_edge_print_on(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    edge = mocker.MagicMock()
    edge.id = "EdgeID"
    edge.parent_id = "ParentID"
    edge.name = "EdgeName"

    visitor = CwpLtlVisitor(mocker.MagicMock())
    visitor.print_on = True

    visitor.write_log_edge(edge)

    expected_call = mocker.call('printf("**EDGE EdgeID(ParentID) = %d\\n", EdgeName)')

    mock_write.assert_has_calls([expected_call])


def test_cwp_write_log_state_print_on(mocker):
    mock_write = mocker.patch.object(CwpLtlVisitor, "write_line")
    state = mocker.MagicMock()
    state.name = "TestState"
    state.id = "StateID"

    visitor = CwpLtlVisitor(mocker.MagicMock())
    visitor.print_on = True

    visitor.write_log_state(state)

    expected_calls = [
        mocker.call("if"),
        mocker.call(":: (TestState) -> "),
        mocker.call('printf("**STATE TestState(StateID)\\n")'),
        mocker.call(":: else -> skip"),
        mocker.call("fi"),
    ]

    mock_write.assert_has_calls(expected_calls, any_order=False)


@pytest.mark.parametrize(
    "print_on, expected_header, expected_footer",
    [
        (
            True,
            "\n\n//**********LOG STATE************//\n\n",
            'printf("******************************\\n")',
        ),
        (False, "\n\n//***********LOG STATE FILLER*******//\n\n", "skip"),
    ],
)
def test_write_log_state_inline(mocker, print_on, expected_header, expected_footer):
    mock_write_line = mocker.patch.object(CwpLtlVisitor, "write_line")
    mock_write_log_state = mocker.patch.object(CwpLtlVisitor, "write_log_state")
    mock_write_log_edge = mocker.patch.object(CwpLtlVisitor, "write_log_edge")
    mock_write_log_var = mocker.patch.object(CwpLtlVisitor, "write_log_var")

    cwp = mocker.MagicMock()
    cwp.states = {
        "state1": mocker.MagicMock(),
        "state2": mocker.MagicMock(),
    }
    cwp.edges = {"edge1": mocker.MagicMock(), "edge2": mocker.MagicMock()}
    state_result = (
        StateBuilder()
        .with_var_decl(VarDecl("var1", "int", AllowedValueDecl("0"), []))
        .with_var_decl(VarDecl("var2", "int", AllowedValueDecl("0"), []))
        .build()
    )
    assert is_successful(state_result)
    state = state_result.unwrap()

    visitor = CwpLtlVisitor(state)
    visitor.cwp = cwp
    visitor.print_on = print_on
    visitor.tab = 0

    visitor.write_log_state_inline()

    expected_calls = [
        mocker.call(expected_header),
        mocker.call("inline logState(){"),
        mocker.call(expected_footer),
        mocker.call(expected_footer),
        mocker.call("}"),
    ]
    mock_write_line.assert_has_calls(expected_calls, any_order=True)

    mock_write_log_state.assert_any_call(cwp.states["state1"])
    mock_write_log_state.assert_any_call(cwp.states["state2"])

    mock_write_log_edge.assert_any_call(cwp.edges["edge1"])
    mock_write_log_edge.assert_any_call(cwp.edges["edge2"])

    mock_write_log_var.assert_any_call("var1")
    mock_write_log_var.assert_any_call("var2")

    assert visitor.tab == 0


def test_generate_all(mocker):
    instance = CwpLtlVisitor(mocker.MagicMock())
    mock_generate_helper_functions = mocker.patch.object(
        instance, "generate_helper_functions"
    )
    mock_generate_LTL = mocker.patch.object(instance, "generate_LTL")

    instance.generate_all()

    mock_generate_helper_functions.assert_called_once()
    mock_generate_LTL.assert_called_once()


def test_generate_helper_functions(mocker):
    instance = CwpLtlVisitor(mocker.MagicMock())
    mock_write_state_variables = mocker.patch.object(instance, "write_state_variables")
    mock_write_variable_range_invariants = mocker.patch.object(
        instance, "write_variable_range_invariants"
    )
    mock_write_init_states = mocker.patch.object(instance, "write_init_states")
    mock_write_edge_definitions = mocker.patch.object(
        instance, "write_edge_definitions"
    )
    mock_write_update_state = mocker.patch.object(instance, "write_update_state")
    mock_write_log_state_inline = mocker.patch.object(
        instance, "write_log_state_inline"
    )

    instance.print_on = True
    instance.generate_helper_functions()
    mock_write_state_variables.assert_called_once()
    mock_write_variable_range_invariants.assert_called_once()
    mock_write_init_states.assert_called_once()
    mock_write_edge_definitions.assert_called_once()
    mock_write_update_state.assert_called_once()
    mock_write_log_state_inline.assert_called_once()

    mock_write_log_state_inline.reset_mock()
    instance.print_on = False
    instance.generate_helper_functions()
    mock_write_log_state_inline.assert_not_called()


def test_generate_LTL(mocker):
    instance = CwpLtlVisitor(mocker.MagicMock())
    instance.cwp = mocker.MagicMock()
    mock_write_global_properties = mocker.patch.object(
        instance, "write_global_properties"
    )
    mock_write_state_properties = mocker.patch.object(
        instance, "write_state_properties"
    )
    mock_write_line = mocker.patch.object(instance, "write_line")

    instance.cwp.states = {
        "state1": mocker.MagicMock(),
        "state2": mocker.MagicMock(),
    }

    instance.generate_LTL()

    mock_write_global_properties.assert_called_once()

    assert mock_write_state_properties.call_count == len(instance.cwp.states)
    mock_write_state_properties.assert_any_call(instance.cwp.states["state1"])
    mock_write_state_properties.assert_any_call(instance.cwp.states["state2"])

    expected_calls = [mocker.call(""), mocker.call(""), mocker.call("")]
    mock_write_line.assert_has_calls(expected_calls)
