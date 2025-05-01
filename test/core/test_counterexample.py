from bpmncwpverify.core.counterexample import CounterExample, NL_SINGLE
import pytest


@pytest.fixture
def get_mock_write_str(mocker):
    return mocker.patch("bpmncwpverify.util.stringmanager.StringManager.write_str")


def test_generate_counter_example(mocker):
    spin_output = mocker.Mock()
    spin_output.stdout = "test_str"
    mocker.patch(
        "bpmncwpverify.core.counterexample.subprocess.run", return_value=spin_output
    )
    mock_filter_spin_trace = mocker.patch(
        "bpmncwpverify.core.counterexample.CounterExample.filter_spin_trace"
    )

    CounterExample.generate_counterexample(mocker.Mock(), mocker.Mock())

    mock_filter_spin_trace.assert_called_once_with("test_str")


def test_filter_spin_trace(get_mock_write_str, mocker):
    mock_write_str = get_mock_write_str

    spin_trace_string = mocker.Mock()
    spin_trace_string.splitlines.return_value = [
        "test string",
        "with random words and",
        "spin:",
        "this text is pointless",
    ]

    CounterExample.filter_spin_trace(spin_trace_string)

    calls = [
        mocker.call("test string", NL_SINGLE),
        mocker.call("with random words and", NL_SINGLE),
    ]

    mock_write_str.assert_has_calls(calls)
