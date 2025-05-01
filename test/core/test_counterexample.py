from bpmncwpverify.core.counterexample import CounterExample


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


def test_filter_spin_trace(mocker):
    pass
