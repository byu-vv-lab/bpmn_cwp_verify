from bpmncwpverify.core.cwp import Cwp, CwpEdge, CwpState, CwpVisitor


class CwpPromelaVisitor(CwpVisitor):  # type: ignore
    def visit_state(self, state: CwpState) -> bool:
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
