from bpmncwpverify.core.counterexample import CounterExample, NL_SINGLE
from bpmncwpverify.core.error import Error
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

    CounterExample.generate_counterexample(
        mocker.Mock(), mocker.MagicMock(__name__="test")
    )

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


def test_counterexample_constructor(mocker):
    class SubError(Error):
        pass

    error_trace = mocker.Mock()

    ce = CounterExample([error_trace], SubError)

    assert ce.trace_steps == [error_trace]
    assert ce.error == "SubError"


def test_counterexample_extract_steps():
    test_string = """ID: test_id\nChanged vars:\ntest_var1\ntest_var2\nCurrent state: test_state1"""
    steps = CounterExample.extract_steps(test_string)
    assert len(steps) == 1
    assert steps[0].id == "test_id"
    assert steps[0].changed_vars == ["test_var1", "test_var2"]
    assert steps[0].curr_cwp_state == ["test_state1"]
