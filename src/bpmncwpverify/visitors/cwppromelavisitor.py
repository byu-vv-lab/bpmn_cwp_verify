from bpmncwpverify.core.cwp import Cwp, CwpEdge, CwpState, CwpVisitor
from bpmncwpverify.util.stringmanager import StringManager, NL_SINGLE


class CwpPromelaVisitor(CwpVisitor):  # type: ignore
    def __init__(self) -> None:
        self.cwp_states = StringManager()

    def visit_state(self, state: CwpState) -> bool:
        new_str = f"bool {state.id} = false \\\\ {state.name}"
        self.cwp_states.write_str(new_str, NL_SINGLE)
        return True

    def end_visit_state(self, state: CwpState) -> None:
        pass

    def visit_edge(self, edge: CwpEdge) -> bool:
        return True

    def end_visit_edge(self, edge: CwpEdge) -> None:
        pass

    def visit_cwp(self, model: Cwp) -> bool:
        return True

    def end_visit_cwp(self, model: Cwp) -> None:
        pass

    def __repr__(self) -> str:
        return str(self.cwp_states)
