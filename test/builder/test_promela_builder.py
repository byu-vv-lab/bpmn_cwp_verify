from bpmncwpverify.builder.promela_builder import PromelaBuilder
from bpmncwpverify.util.stringmanager import NL_SINGLE, IndentAction


def test_logger_generator(mocker):
    mocker.patch.object(
        PromelaBuilder, "variable_name_extractor", return_value=["test_string"]
    )
    mock_write_str = mocker.patch(
        "bpmncwpverify.builder.promela_builder.StringManager.write_str"
    )

    sb = PromelaBuilder()
    state = mocker.Mock()

    mock_val1 = mocker.Mock()
    mock_val1.name = "test_val1"
    mock_val2 = mocker.Mock()
    mock_val2.name = "test_val2"

    cwp = mocker.Mock(states={"_0": mock_val1, "_1": mock_val2})
    sb.logger_generator(state, cwp)

    calls = [
        mocker.call("inline stateLogger(){", NL_SINGLE, IndentAction.INC),
        mocker.call('printf("Changed Vars: \\n");', NL_SINGLE),
        mocker.call("if", NL_SINGLE, IndentAction.INC),
        mocker.call(
            ":: test_string != old_test_string ->", NL_SINGLE, IndentAction.INC
        ),
        mocker.call('printf("test_string = %e\\n", test_string);', NL_SINGLE),
        mocker.call("old_test_string = test_string", NL_SINGLE),
        mocker.call(":: else -> skip", NL_SINGLE, IndentAction.DEC),
        mocker.call("fi;", NL_SINGLE, IndentAction.DEC),
        mocker.call("if", NL_SINGLE, IndentAction.INC),
        mocker.call(":: test_val1 == true ->", NL_SINGLE, IndentAction.INC),
        mocker.call('printf("Current state: test_val1\\n");', NL_SINGLE),
        mocker.call(":: else -> skip", NL_SINGLE, IndentAction.DEC),
        mocker.call("fi;", NL_SINGLE, IndentAction.DEC),
        mocker.call("if", NL_SINGLE, IndentAction.INC),
        mocker.call(":: test_val2 == true ->", NL_SINGLE, IndentAction.INC),
        mocker.call('printf("Current state: test_val2\\n");', NL_SINGLE),
        mocker.call(":: else -> skip", NL_SINGLE, IndentAction.DEC),
        mocker.call("fi;", NL_SINGLE, IndentAction.DEC),
        mocker.call("}", NL_SINGLE, IndentAction.DEC),
    ]
    mock_write_str.assert_has_calls(calls)


def test_variable_name_extractor(mocker):
    vars = [mocker.Mock(id=1), mocker.Mock(id=2)]

    state = mocker.Mock()
    state.vars = vars

    sb = PromelaBuilder()

    result = sb.variable_name_extractor(state)

    assert result == [1, 2]
