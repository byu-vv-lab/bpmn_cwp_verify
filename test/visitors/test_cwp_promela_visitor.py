from bpmncwpverify.visitors.cwppromelavisitor import (
    CwpPromelaVisitor,
    START_STR,
    END_STR,
)
import pytest

from bpmncwpverify.util.stringmanager import (
    NL_SINGLE,
    NL_DOUBLE,
    IndentAction,
)


class TestCwpPromelaVisitor:
    @pytest.fixture
    def get_mock_write_str(self, mocker):
        return mocker.patch("bpmncwpverify.util.stringmanager.StringManager.write_str")

    def test_visit_cwp(self, get_mock_write_str, mocker):
        mock_write_str = get_mock_write_str
        CwpPromelaVisitor().visit_cwp(mocker.Mock())
        mock_write_str.assert_called_once_with(START_STR, 1)

    def test_end_visit_cwp(self, get_mock_write_str, mocker):
        mock_write_str = get_mock_write_str
        CwpPromelaVisitor().end_visit_cwp(mocker.Mock())

        calls = [
            mocker.call(END_STR, NL_DOUBLE),
            mocker.call("inline Update_State() {", NL_SINGLE, IndentAction.INC),
            mocker.call("}", NL_SINGLE, IndentAction.DEC),
            # mocker.call(END_STR, NL_DOUBLE),
        ]

        mock_write_str.assert_has_calls(calls)

    # def test_mapping_function(self, get_mock_write_str, mocker):
    # mock_write_str = get_mock_write_str
    # CwpPromelaVisitor().create_update_state_inline(mocker.Mock())

    def test_visit_state(self, get_mock_write_str, mocker):
        mock_state = mocker.Mock()
        mock_state.name = "test"
        mock_write_str = get_mock_write_str
        CwpPromelaVisitor().visit_state(mock_state)
        mock_write_str.assert_called_once_with("bool test = false", 1)
