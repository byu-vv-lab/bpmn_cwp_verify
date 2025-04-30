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

    def test_create_update_state_inline(self, get_mock_write_str, mocker):
        mock_write_str = get_mock_write_str
        cpv = CwpPromelaVisitor()
        mapping_function = mocker.Mock()
        cpv.mapping_function = mapping_function
        cpv.create_update_state_inline()

        calls = [
            mocker.call("inline updateState() {", NL_SINGLE, IndentAction.INC),
            mocker.call("if", NL_SINGLE, IndentAction.INC),
            mocker.call(mapping_function),
            mocker.call(":: else -> assert false", NL_SINGLE),
            mocker.call("fi", NL_SINGLE, IndentAction.DEC),
            mocker.call("}", NL_SINGLE, IndentAction.DEC),
        ]

        mock_write_str.assert_has_calls(calls)

    def test_end_visit_cwp(self, get_mock_write_str, mocker):
        mock_write_str = get_mock_write_str

        visitor = CwpPromelaVisitor()

        mock_create_update = mocker.patch.object(visitor, "create_update_state_inline")

        visitor.end_visit_cwp(mocker.Mock())

        mock_write_str.assert_called_once_with(END_STR, NL_DOUBLE)
        mock_create_update.assert_called_once()

    def test_visit_state(self, get_mock_write_str, mocker):
        mock_state = mocker.Mock()
        mock_state.name = "test"
        mock_write_str = get_mock_write_str
        CwpPromelaVisitor().visit_state(mock_state)
        mock_write_str.assert_called_once_with("bool test = false", 1)

    def test_build_mapping_function_block(self, get_mock_write_str, mocker):
        mock_write_str = get_mock_write_str

        mock_state = mocker.Mock()
        mock_state.name = "test_name"
        visitor = CwpPromelaVisitor()

        mock_build_mapping_function = mocker.patch.object(
            visitor, "_build_mapping_function", return_value="test_val"
        )
        visitor._build_mapping_function_block(mock_state)

        mock_build_mapping_function.assert_called_once()

        calls = [
            mocker.call(":: ("),
            mocker.call("test_val"),
            mocker.call(") ->", NL_SINGLE, IndentAction.INC),
            mocker.call("test_name = true", NL_SINGLE),
            mocker.call("", indent_action=IndentAction.DEC),
        ]

        mock_write_str.assert_has_calls(calls)
