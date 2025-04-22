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
    sb.logger_generator(mocker.Mock())

    calls = [
        mocker.call("inline stateLogger(){", NL_SINGLE, IndentAction.INC),
        mocker.call('printf("test_string = %s\\n", test_string)', NL_SINGLE),
        mocker.call("}", NL_SINGLE, IndentAction.DEC),
    ]
    mock_write_str.assert_has_calls(calls)
