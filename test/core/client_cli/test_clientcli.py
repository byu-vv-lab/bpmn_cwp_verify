from bpmncwpverify.client_cli.clientcli import process_command
import sys


def test_givin_good_state(capsys):
    test_args = [
        "verify",
        "./test/resources/simple_example/state.txt",
        "./test/resources/simple_example/test_cwp.xml",
        "./test/resources/simple_example/test_bpmn.bpmn",
    ]
    sys.argv = test_args

    result = process_command()
    print(result)
