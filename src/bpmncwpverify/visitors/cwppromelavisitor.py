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
        # self.start = StringManager()
        self.cwp_states = StringManager()
        self.update_state_inline = StringManager()
        # self.end = StringManager()

    def visit_state(self, state: CwpState) -> bool:
        new_str = f"bool {state.name} = false"
        self.cwp_states.write_str(new_str, NL_SINGLE)
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

        self.update_state_inline.write_str("}", NL_SINGLE, IndentAction.DEC)
        # self.update_state_inline.write_str(END_STR, NL_DOUBLE)
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
