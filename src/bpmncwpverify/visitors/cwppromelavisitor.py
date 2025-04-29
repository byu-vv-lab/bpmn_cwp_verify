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

    def visit_state(self, state: CwpState) -> bool:
        new_str = f"bool {state.name} = false"
        self.cwp_states.write_str(new_str, NL_SINGLE)

        # input edges
        self.mapping_function.write_str("::((")
        for edge in state.in_edges:
            self.mapping_function.write_str(f"{edge.expression} && ")

        # ensure the ending in && doesnt break the promela
        self.mapping_function.write_str("true ")

        self.mapping_function.write_str(") && !(")

        for edge in state.out_edges:
            self.mapping_function.write_str(f"{edge.expression} ||")

        # ensure the ending in || doesnt break the promela
        self.mapping_function.write_str("false ")

        self.mapping_function.write_str(f")) -> {state.name} = true", NL_SINGLE)

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
        self.update_state_inline.write_str(self.mapping_function, NL_SINGLE)

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
