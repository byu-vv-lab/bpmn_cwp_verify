# type: ignore
import pytest
from returns.maybe import Some

from bpmncwpverify.builder.promela_builder import (
    _generate_logger,
    _generate_state_dump,
    _generate_state_promela,
)
from bpmncwpverify.core.state import State
from bpmncwpverify.util.stringmanager import NL_DOUBLE, NL_SINGLE, IndentAction


def test_logger_generator(mocker):
    mock_write_str = mocker.patch(
        "bpmncwpverify.builder.promela_builder.StringManager.write_str"
    )

    mock_val1 = mocker.Mock()
    mock_val1.name = "test_val1"
    mock_val1.id = "test_string1"
    mock_val1.type_ = "bool"
    mock_val2 = mocker.Mock()
    mock_val2.name = "test_val2"
    mock_val2.id = "test_string2"
    mock_val2.type_ = "byte"

    state = mocker.Mock()
    state.vars = [mock_val1, mock_val2]
    state.arrays = []
    state.str2var = {var.id: var for var in state.vars}

    cwp = mocker.Mock(states={"_0": mock_val1, "_1": mock_val2})
    _generate_logger(state, cwp)

    calls = [
        mocker.call("inline stateLogger(){", NL_SINGLE, IndentAction.INC),
        mocker.call('printf("Changed Vars: \\n")', NL_SINGLE),
        mocker.call("if", NL_SINGLE, IndentAction.INC),
        mocker.call(
            ":: test_string1 != old_test_string1 ->", NL_SINGLE, IndentAction.INC
        ),
        mocker.call('printf("test_string1 = %d\\n", test_string1)', NL_SINGLE),
        mocker.call("old_test_string1 = test_string1", NL_SINGLE),
        mocker.call(":: else", NL_SINGLE, IndentAction.DEC),
        mocker.call("fi;", NL_SINGLE, IndentAction.DEC),
        mocker.call("if", NL_SINGLE, IndentAction.INC),
        mocker.call(
            ":: test_string2 != old_test_string2 ->", NL_SINGLE, IndentAction.INC
        ),
        mocker.call('printf("test_string2 = %u\\n", test_string2)', NL_SINGLE),
        mocker.call("old_test_string2 = test_string2", NL_SINGLE),
        mocker.call(":: else", NL_SINGLE, IndentAction.DEC),
        mocker.call("fi;", NL_SINGLE, IndentAction.DEC),
        mocker.call("if", NL_SINGLE, IndentAction.INC),
        mocker.call(":: test_val1 == true ->", NL_SINGLE, IndentAction.INC),
        mocker.call('printf("Current state: test_val1\\n")', NL_SINGLE),
        mocker.call(":: else", NL_SINGLE, IndentAction.DEC),
        mocker.call("fi;", NL_SINGLE, IndentAction.DEC),
        mocker.call("if", NL_SINGLE, IndentAction.INC),
        mocker.call(":: test_val2 == true ->", NL_SINGLE, IndentAction.INC),
        mocker.call('printf("Current state: test_val2\\n")', NL_SINGLE),
        mocker.call(":: else", NL_SINGLE, IndentAction.DEC),
        mocker.call("fi;", NL_SINGLE, IndentAction.DEC),
        mocker.call("}", NL_DOUBLE, IndentAction.DEC),
    ]
    mock_write_str.assert_has_calls(calls)


def test_state_dump_int(mocker):
    vars = [
        mocker.Mock(id="v1", type_="int", init="1"),
        mocker.Mock(id="v2", type_="int", init="2"),
    ]

    state = mocker.Mock()
    state.vars = vars
    state.arrays = []
    state.str2var = {var.id: var for var in vars}

    result = _generate_state_dump(state)

    assert (
        result
        == 'inline stateDump(){\n\tprintf("v1 = %d\\n", v1)\n\tprintf("v2 = %d\\n", v2)\n}\n\n'
    )


def test_state_dump_bool(mocker):
    vars = [
        mocker.Mock(id="v1", type_="bool", init="true"),
        mocker.Mock(id="v2", type_="bool", init="true"),
    ]

    state = mocker.Mock()
    state.vars = vars
    state.arrays = []
    state.str2var = {var.id: var for var in vars}
    result = _generate_state_dump(state)

    assert (
        result
        == 'inline stateDump(){\n\tprintf("v1 = %d\\n", v1)\n\tprintf("v2 = %d\\n", v2)\n}\n\n'
    )


def test_state_dump_enum(mocker):
    vars = [
        mocker.Mock(id="v1", type_="BinDecision", init="yes"),
        mocker.Mock(id="v2", type_="BinDecision", init="no"),
    ]

    state = mocker.Mock()
    state.vars = vars
    state.arrays = []
    state.str2var = {var.id: var for var in vars}

    result = _generate_state_dump(state)

    assert (
        result
        == 'inline stateDump(){\n\tprintf("v1 = %e\\n", v1)\n\tprintf("v2 = %e\\n", v2)\n}\n\n'
    )


def test_state_dump_typedef(mocker):
    vars = [mocker.Mock(id="v1", type_="int", init="1")]

    state = mocker.Mock()
    state.vars = vars
    state.arrays = []
    state.typedefs = [
        mocker.Mock(
            id="OuterTypedef",
            fields=[mocker.Mock(id="field1", type_="int", init="0")],
            nested_typedefs=[
                mocker.Mock(
                    id="NestedTypedef",
                    fields=[mocker.Mock(id="nested_field", type_="int", init="1")],
                )
            ],
        )
    ]
    state.str2var = {
        "v1": vars[0],
        "OuterTypedef.field1": state.typedefs[0].fields[0],
        "NestedTypedef.nested_field": state.typedefs[0].nested_typedefs[0].fields[0],
    }

    result = _generate_state_dump(state)

    assert (
        result
        == 'inline stateDump(){\n\tprintf("v1 = %d\\n", v1)\n\tprintf("OuterTypedef.field1 = %d\\n", OuterTypedef.field1)\n\tprintf("NestedTypedef.nested_field = %d\\n", NestedTypedef.nested_field)\n}\n\n'
    )


def test_generate_promela(mocker):
    const = mocker.Mock(id="const_id", init=mocker.Mock(value="const_init_val"))
    enum = mocker.Mock(
        id="enum_id",
        values=[mocker.Mock(value="init_val"), mocker.Mock(value="other_val")],
    )
    var1 = mocker.Mock(id="var1_id", type_="int", init=mocker.Mock(value="0"))
    var2 = mocker.Mock(
        id="var2_id", type_="enum_id", init=mocker.Mock(value="init_val")
    )
    var3 = mocker.Mock(id="var3_id", type_="bool", init=mocker.Mock(value="0"))
    var4 = mocker.Mock(id="var4_id", type_="bit", init=mocker.Mock(value="0"))

    array = mocker.Mock(
        id="array_id",
        type_="int",
        size=5,
        values=[
            mocker.Mock(value="1"),
            mocker.Mock(value="2"),
            mocker.Mock(value="3"),
            mocker.Mock(value="4"),
            mocker.Mock(value="5"),
        ],
    )
    var5 = mocker.Mock(
        id="outertypedef", type_="typedef", init=mocker.Mock(value="OuterTypedef")
    )
    typedef2 = mocker.Mock(
        id="InnerTypedef",
        fields=[
            mocker.Mock(id="nested_field", type_="int", init=mocker.Mock(value="1"))
        ],
    )
    typedef1 = mocker.Mock(
        id="OuterTypedef",
        fields=[
            mocker.Mock(id="field1", type_="int", init=mocker.Mock(value="0")),
            mocker.Mock(
                id="innertypedef",
                type_="typedef",
                init=mocker.Mock(value="InnerTypedef"),
            ),
        ],
        nested_typedefs=[typedef2],
    )

    _consts = [const]
    _vars = [var1, var2, var3, var4, var5]
    _enums = [enum]
    _arrays = [array]
    _typedefs = [typedef2, typedef1]

    state = State(_consts, _enums, _vars, _arrays, _typedefs)
    state._str2var = Some(
        {
            "var1_id": var1,
            "var2_id": var2,
            "var3_id": var3,
            "var4_id": var4,
            "outertypedef": var5,
            "outertypedef.field1": typedef1.fields[0],
            "outertypedef.innertypedef.nested_field": typedef1.nested_typedefs[
                0
            ].fields[0],
        }
    )
    result = _generate_state_promela(state)

    expected = (
        "//**********VARIABLE DECLARATION************//\n"
        "#define const_id const_init_val\n"
        "mtype:enum_id = {init_val other_val}\n"
        "int array_id[5] = {1, 2, 3, 4, 5}\n"
        "hidden int old_array_id[5] = {1, 2, 3, 4, 5}\n"
        "typedef InnerTypedef {\n    int nested_field\n}\n"
        "typedef OuterTypedef {\n    int field1\n    InnerTypedef innertypedef\n}\n"
        "int var1_id = 0\n"
        "hidden int old_var1_id = var1_id\n"
        "mtype:enum_id var2_id = init_val\n"
        "hidden mtype:enum_id old_var2_id = var2_id\n"
        "bool var3_id = 0\n"
        "bool old_var3_id = var3_id\n"
        "bit var4_id = 0\n"
        "bit old_var4_id = var4_id\n"
        "OuterTypedef outertypedef\n"
        "OuterTypedef old_outertypedef\n"
        "inline typedefInit() {\n    outertypedef.field1 = 0\n    old_outertypedef.field1 = 0\n    outertypedef.innertypedef.nested_field = 1\n    old_outertypedef.innertypedef.nested_field = 1\n}\n\n"
    )
    assert result == expected


@pytest.fixture
def mock_state(mocker):
    """Fixture to create a mock State object."""
    state = mocker.MagicMock()
    state._consts = []
    state._enums = []
    state._vars = []
    state._arrays = []
    state._typedefs = []
    return state


def test_generate_promela_with_full_state(mocker, mock_state):
    """Test generate_promela with a state containing constants, enums, and variables."""

    mock_const = mocker.MagicMock()
    mock_const.id = "MAX_COUNT"
    mock_const.init.value = "10"

    mock_enum = mocker.MagicMock()
    mock_enum.id = "TestEnum"
    mock_enum.values = [mocker.MagicMock(value="START"), mocker.MagicMock(value="STOP")]

    mock_var_enum = mocker.MagicMock()
    mock_var_enum.type_ = "int"
    mock_var_enum.id = "state_var"
    mock_var_enum.init.value = "START"

    mock_var_int = mocker.MagicMock()
    mock_var_int.type_ = "int"
    mock_var_int.id = "counter"
    mock_var_int.init.value = "0"

    mock_array = mocker.MagicMock()
    mock_array.type_ = "int"
    mock_array.id = "array_id"
    mock_array.size = 5
    mock_array.values = [
        mocker.Mock(value="1"),
        mocker.Mock(value="2"),
        mocker.Mock(value="3"),
        mocker.Mock(value="4"),
        mocker.Mock(value="5"),
    ]

    mock_var_typedef = mocker.MagicMock()
    mock_var_typedef.type_ = "typedef"
    mock_var_typedef.id = "outer_typedef"
    mock_var_typedef.init.value = "OuterTypedef"

    mock_typedef1 = mocker.MagicMock()
    mock_typedef1.id = "InnerTypedef"
    mock_typedef1.fields = [
        mocker.MagicMock(
            id="inner_field1", type_="int", init=mocker.MagicMock(value="1")
        )
    ]
    mock_typedef1.nested_typedefs = []

    mock_typedef2 = mocker.MagicMock()
    mock_typedef2.id = "OuterTypedef"
    mock_typedef2.fields = [
        mocker.MagicMock(
            id="outer_field1", type_="int", init=mocker.MagicMock(value="0")
        ),
        mocker.MagicMock(
            id="inner_typedef",
            type_="typedef",
            init=mocker.MagicMock(value="InnerTypedef"),
        ),
    ]
    mock_typedef2.nested_typedefs = [mock_typedef1]

    mock_state.consts = [mock_const]
    mock_state.enums = [mock_enum]
    mock_state.vars = [mock_var_enum, mock_var_int, mock_var_typedef]
    mock_state.typedefs = [mock_typedef1, mock_typedef2]
    mock_state.str2var = {
        "state_var": mock_var_enum,
        "counter": mock_var_int,
        "outer_typedef": mock_var_typedef,
        "outer_typedef.outer_field1": mock_typedef2.fields[0],
        "outer_typedef.inner_typedef.inner_field1": mock_typedef1.fields[0],
    }
    mock_state.arrays = [mock_array]

    result = _generate_state_promela(mock_state)

    expected_output = (
        "//**********VARIABLE DECLARATION************//\n"
        "#define MAX_COUNT 10\n"
        "mtype:TestEnum = {START STOP}\n"
        "int array_id[5] = {1, 2, 3, 4, 5}\n"
        "hidden int old_array_id[5] = {1, 2, 3, 4, 5}\n"
        "typedef InnerTypedef {\n    int inner_field1\n}\n"
        "typedef OuterTypedef {\n    int outer_field1\n    InnerTypedef inner_typedef\n}\n"
        "int state_var = START\n"
        "hidden int old_state_var = state_var\n"
        "int counter = 0\n"
        "hidden int old_counter = counter\n"
        "OuterTypedef outer_typedef\n"
        "OuterTypedef old_outer_typedef\n"
        "inline typedefInit() {\n    outer_typedef.outer_field1 = 0\n    old_outer_typedef.outer_field1 = 0\n    outer_typedef.inner_typedef.inner_field1 = 1\n    old_outer_typedef.inner_typedef.inner_field1 = 1\n}\n\n"
    )

    assert result == expected_output


def test_generate_promela_with_only_constants(mocker, mock_state):
    """Test generate_promela with only constants."""

    mock_const = mocker.MagicMock()
    mock_const.id = "BUFFER_SIZE"
    mock_const.init.value = "256"

    mock_state.consts = [mock_const]

    result = _generate_state_promela(mock_state)

    expected_output = (
        "//**********VARIABLE DECLARATION************//\n#define BUFFER_SIZE 256\n"
        "inline typedefInit() {\n    skip\n}\n\n"
    )

    assert result == expected_output


def test_generate_promela_with_only_enums(mocker, mock_state):
    """Test generate_promela with only enums."""

    mock_enum = mocker.MagicMock()
    mock_enum.id = "TestEnum"
    mock_enum.values = [
        mocker.MagicMock(value="IDLE"),
        mocker.MagicMock(value="RUNNING"),
    ]

    mock_state.enums = [mock_enum]

    result = _generate_state_promela(mock_state)

    expected_output = (
        "//**********VARIABLE DECLARATION************//\n"
        "mtype:TestEnum = {IDLE RUNNING}\n"
        "inline typedefInit() {\n    skip\n}\n\n"
    )

    assert result == expected_output


def test_generate_promela_with_only_typedefs(mocker, mock_state):
    """Test generate_promela with only typedefs."""

    mock_typedef3 = mocker.MagicMock()
    mock_typedef3.id = "InnerStruct"
    mock_typedef3.fields = [
        mocker.MagicMock(
            id="inner_field1", type_="int", init=mocker.MagicMock(value="1")
        )
    ]
    mock_typedef3.nested_typedefs = []

    mock_typedef1 = mocker.MagicMock()
    mock_typedef1.id = "MyStruct"
    mock_typedef1.fields = [
        mocker.MagicMock(id="field1", type_="bit", init=mocker.MagicMock(value="1")),
        mocker.MagicMock(id="field2", type_="bit", init=mocker.MagicMock(value="0")),
    ]
    mock_typedef1.nested_typedefs = [mock_typedef3]

    mock_typedef2 = mocker.MagicMock()
    mock_typedef2.id = "MyOtherStruct"
    mock_typedef2.fields = [
        mocker.MagicMock(id="field3", type_="int", init=mocker.MagicMock(value="10")),
        mocker.MagicMock(id="field4", type_="int", init=mocker.MagicMock(value="'11'")),
    ]
    mock_typedef2.nested_typedefs = []

    mock_state.typedefs = [mock_typedef3, mock_typedef1, mock_typedef2]

    result = _generate_state_promela(mock_state)

    expected_output = (
        "//**********VARIABLE DECLARATION************//\n"
        "typedef InnerStruct {\n"
        "    int inner_field1\n"
        "}\n"
        "typedef MyStruct {\n"
        "    bit field1\n"
        "    bit field2\n"
        "}\n"
        "typedef MyOtherStruct {\n"
        "    int field3\n"
        "    int field4\n"
        "}\n"
        "inline typedefInit() {\n    skip\n}\n\n"
    )

    assert result == expected_output


def test_generate_promela_with_only_arrays(mocker, mock_state):
    """Test generate_promela with only arrays."""

    mock_array = mocker.MagicMock()
    mock_array.type_ = "int"
    mock_array.id = "array_id"
    mock_array.size = 5
    mock_array.values = [
        mocker.Mock(value="1"),
        mocker.Mock(value="2"),
        mocker.Mock(value="3"),
        mocker.Mock(value="4"),
        mocker.Mock(value="5"),
    ]

    mock_state.arrays = [mock_array]

    result = _generate_state_promela(mock_state)

    expected_output = (
        "//**********VARIABLE DECLARATION************//\n"
        "int array_id[5] = {1, 2, 3, 4, 5}\n"
        "hidden int old_array_id[5] = {1, 2, 3, 4, 5}\n"
        "inline typedefInit() {\n    skip\n}\n\n"
    )

    assert result == expected_output


def test_generate_promela_with_empty_state(mock_state):
    """Test generate_promela with an empty state."""

    result = _generate_state_promela(mock_state)

    expected_output = (
        "//**********VARIABLE DECLARATION************//\n"
        "inline typedefInit() {\n    skip\n}\n\n"
    )

    assert result == expected_output
