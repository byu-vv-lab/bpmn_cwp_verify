from bpmncwpverify.core.cwp import Cwp, CwpEdge, CwpState, CwpVisitor
from bpmncwpverify.util.stringmanager import StringManager, NL_SINGLE, NL_DOUBLE

START_STR = "//**********CWP VARIABLE DECLARATION************//"
END_STR = "//**********************************************//"


class CwpPromelaVisitor(CwpVisitor):  # type: ignore
    def __init__(self) -> None:
        self.start = StringManager()
        self.cwp_states = StringManager()
        self.end = StringManager()

    def visit_state(self, state: CwpState) -> bool:
        new_str = f"bool {state.name} = false // {state.name}"
        self.cwp_states.write_str(new_str, NL_SINGLE)
        return True

    def end_visit_state(self, state: CwpState) -> None:
        pass

    def visit_edge(self, edge: CwpEdge) -> bool:
        return True

    def end_visit_edge(self, edge: CwpEdge) -> None:
        pass

    def visit_cwp(self, model: Cwp) -> bool:
        self.start.write_str(START_STR, NL_SINGLE)
        return True

    def end_visit_cwp(self, model: Cwp) -> None:
        self.end.write_str(END_STR, NL_DOUBLE)
        pass

    def __repr__(self) -> str:
        return f"{self.start}{self.cwp_states}{self.end}"
