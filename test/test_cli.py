# type: ignore
from bpmncwpverify.cli import verify
import sys


def test_verify(capsys):
    test_args = [
        "verify",
        "./test/state.txt",
        "./test/resources/test_cwp.xml",
        "./test/resources/test_bpmn.bpmn",
        "./test/resources/behavior.txt",
    ]
    sys.argv = test_args
    verify()
    captured = capsys.readouterr()
    assert captured.out == "Hello, Alice!\n"
