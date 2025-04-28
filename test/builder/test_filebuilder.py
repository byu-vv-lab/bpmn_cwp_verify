from bpmncwpverify.builder.filebuilder import StateBuilder
from bpmncwpverify.util.stringmanager import NL_SINGLE, IndentAction


def test_logger_generator(mocker):
    mocker.patch.object(
        StateBuilder, "variable_name_extractor", return_value=["test_string"]
    )
    mock_write_str = mocker.patch(
        "bpmncwpverify.builder.filebuilder.StringManager.write_str"
    )

    sb = StateBuilder()
    state = mocker.Mock(_vars=[])  # TODO: change _vars to not be empty for future tests
    sb.logger_generator(state)

    calls = [
        mocker.call("inline stateLogger(){", NL_SINGLE, IndentAction.INC),
        mocker.call("if", NL_SINGLE, IndentAction.INC),
        mocker.call(
            ":: test_string != old_test_string ->", NL_SINGLE, IndentAction.INC
        ),
        mocker.call('printf("test_string = %s\\n", test_string)', NL_SINGLE),
        mocker.call("old_test_string = test_string", NL_SINGLE),
        mocker.call(":: else -> skip", NL_SINGLE, IndentAction.DEC),
        mocker.call("fi", NL_SINGLE, IndentAction.DEC),
        mocker.call("}", NL_SINGLE, IndentAction.DEC),
    ]
    mock_write_str.assert_has_calls(calls)


def test_variable_name_extractor(mocker):
    vars = [mocker.Mock(id=1), mocker.Mock(id=2)]

    state = mocker.Mock()
    state._vars = vars

    sb = StateBuilder()

    result = sb.variable_name_extractor(state)

    assert result == [1, 2]
