from bpmncwpverify.core.cwp import Cwp, CwpEdge, CwpState, CwpVisitor
from bpmncwpverify.util.stringmanager import (
    StringManager,
    NL_SINGLE,
    NL_DOUBLE,
    IndentAction,
)

START_STR = "//**********CWP VARIABLE DECLARATION************//"
END_STR = "//**********************************************//"


class CwpPromelaVisitor(CwpVisitor):  # type: ignore
    def __init__(self) -> None:
        self.cwp_states = StringManager()
        self.update_state_inline = StringManager()
        self.mapping_function = StringManager()

    def _build_mapping_function(self, state: CwpState) -> StringManager:
        guard = StringManager()

        guard.write_str("(")
        guard.write_str(
            " && ".join(
                [f"{edge.expression}" for edge in state.in_edges]
                if state.in_edges
                else ["true"]
            )
        )  # ["true"] in case no in edges

        guard.write_str(") && !(")

        guard.write_str(
            " || ".join(
                [f"{edge.expression}" for edge in state.out_edges]
                if state.out_edges
                else ["false"]
            )
        )  # ["false"] in case no out edges

        guard.write_str(")")

        return guard

    def _build_mapping_function_block(self, state: CwpState) -> None:
        mapping_func = self._build_mapping_function(state)

        self.mapping_function.write_str(":: (")
        self.mapping_function.write_str(mapping_func)
        self.mapping_function.write_str(") ->", NL_SINGLE, IndentAction.INC)
        self.mapping_function.write_str(f"{state.name} = true", NL_SINGLE)
        self.mapping_function.write_str("", indent_action=IndentAction.DEC)

    def visit_state(self, state: CwpState) -> bool:
        new_str = f"bool {state.name} = false"
        self.cwp_states.write_str(new_str, NL_SINGLE)

        self._build_mapping_function_block(state)

        return True

    def end_visit_state(self, state: CwpState) -> None:
        pass

    def visit_edge(self, edge: CwpEdge) -> bool:
        return True

    def create_update_state_inline(
        self,
    ) -> None:
        new_str = "inline Update_State() {"
        self.update_state_inline.write_str(new_str, NL_SINGLE, IndentAction.INC)

        # inside of update state inline will go here

        # start of the if statement
        self.update_state_inline.write_str("if", NL_SINGLE, IndentAction.INC)

        # update state inline sm appends mapping function sm
        self.update_state_inline.write_str(self.mapping_function)

        self.update_state_inline.write_str(":: else -> assert false", NL_SINGLE)

        # end of if statement
        self.update_state_inline.write_str("fi", NL_SINGLE, IndentAction.DEC)

        self.update_state_inline.write_str("}", NL_SINGLE, IndentAction.DEC)
        pass

    def end_visit_edge(self, edge: CwpEdge) -> None:
        pass

    def visit_cwp(self, model: Cwp) -> bool:
        self.cwp_states.write_str(START_STR, NL_SINGLE)
        return True

    def end_visit_cwp(self, model: Cwp) -> None:
        self.cwp_states.write_str(END_STR, NL_DOUBLE)
        self.create_update_state_inline()
        pass

    def __repr__(self) -> str:
        return f"{self.cwp_states}{self.update_state_inline}"
