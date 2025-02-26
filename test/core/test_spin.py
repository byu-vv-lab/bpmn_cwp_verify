# type: ignore
from bpmncwpverify.core.spin import SpinOutput
from returns.result import Failure, Success


def test_check_syntax_errors(mocker):
    spin_output = SpinOutput()
    s = """
    spin: test/resources/simple_example/valid_output.pml:55, Error: syntax error    saw ''}' = 125'
    spin: test/resources/simple_example/valid_output.pml:116, Error: missing '}' ?
    """

    result = spin_output._check_syntax_errors(s)

    assert isinstance(result, Failure)
    result = result.failure()
    assert (
        result.list_of_error_maps[0]["file_path"]
        == "test/resources/simple_example/valid_output.pml"
    )
    assert (
        result.list_of_error_maps[1]["file_path"]
        == "test/resources/simple_example/valid_output.pml"
    )

    assert result.list_of_error_maps[0]["line_number"] == "55"
    assert result.list_of_error_maps[1]["line_number"] == "116"

    assert result.list_of_error_maps[0]["error_msg"] == "syntax error saw ''}' = 125'"
    assert result.list_of_error_maps[1]["error_msg"] == "missing '}' ?"


def test_check_syntax_errors_none(mocker):
    spin_output = SpinOutput()
    s = """
        (Spin Version 6.5.2 -- 6 December 2019)
                + Partial Order Reduction

        Full statespace search for:
                never claim             - (none specified)
                assertion violations    +
                cycle checks            - (disabled by -DSAFETY)
                invalid end states      +
        ...
    """

    result = spin_output._check_syntax_errors(s)

    assert isinstance(result, Success)
