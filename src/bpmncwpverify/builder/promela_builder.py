from returns.result import Failure, Result, Success

from bpmncwpverify.core.bpmn import Bpmn
from bpmncwpverify.core.cwp import Cwp
from bpmncwpverify.core.error import Error, NotInitializedError
from bpmncwpverify.core.state import State
from bpmncwpverify.util.stringmanager import NL_SINGLE, IndentAction, StringManager
from bpmncwpverify.visitors.bpmn_promela_visitor import PromelaGenVisitor
from bpmncwpverify.visitors.cwp_promela_visitor import CwpPromelaVisitor


def _generate_bpmn_promela(bpmn: Bpmn) -> str:
    promela_visitor = PromelaGenVisitor()
    bpmn.accept(promela_visitor)
    return str(promela_visitor)


def _generate_cwp_promela(cwp: Cwp, state: State) -> str:
    ltl_visitor = CwpPromelaVisitor()
    cwp.accept(ltl_visitor)
    return str(ltl_visitor)


def _generate_logger(state: State, cwp: Cwp) -> str:
    var_names = _get_variable_names(state)
    loggerFunction = StringManager()

    loggerFunction.write_str("inline stateLogger(){", NL_SINGLE, IndentAction.INC)
    loggerFunction.write_str('printf("Changed Vars: \\n");', NL_SINGLE)
    for name in var_names:
        loggerFunction.write_str("if", NL_SINGLE, IndentAction.INC)
        loggerFunction.write_str(
            f":: {name} != old_{name} ->", NL_SINGLE, IndentAction.INC
        )
        loggerFunction.write_str(f'printf("{name} = %e\\n", {name});', NL_SINGLE)
        loggerFunction.write_str(f"old_{name} = {name}", NL_SINGLE)
        loggerFunction.write_str(":: else -> skip", NL_SINGLE, IndentAction.DEC)
        loggerFunction.write_str("fi;", NL_SINGLE, IndentAction.DEC)

    for cwp_state in cwp.states.values():
        loggerFunction.write_str("if", NL_SINGLE, IndentAction.INC)
        loggerFunction.write_str(
            f":: {cwp_state.name} == true ->", NL_SINGLE, IndentAction.INC
        )
        loggerFunction.write_str(
            f'printf("Current state: {cwp_state.name}\\n");', NL_SINGLE
        )
        loggerFunction.write_str(":: else -> skip", NL_SINGLE, IndentAction.DEC)
        loggerFunction.write_str("fi;", NL_SINGLE, IndentAction.DEC)
    loggerFunction.write_str("}", NL_SINGLE, IndentAction.DEC)
    return str(loggerFunction)


def _generate_promela(state: State, cwp: Cwp, bpmn: Bpmn) -> Result[str, Error]:
    cwp_pml = _generate_cwp_promela(cwp, state)
    vars_pml = _generate_state_promela(state)
    logger_pml = _generate_logger(state, cwp)
    bpmn_pml = _generate_bpmn_promela(bpmn)
    pml = f"{vars_pml}{cwp_pml}{logger_pml}{bpmn_pml}"
    return Success(pml)


def _generate_state_promela(state: State) -> str:
    return State.generate_promela(state)


def _get_variable_names(state: State) -> list[str]:
    variableNames: list[str] = []
    for var in state.vars:
        variableNames.append(var.id)
    return variableNames


class PromelaBuilder:
    __slots__ = [
        "bpmn",
        "cwp",
        "state",
    ]

    def __init__(self) -> None:
        self.bpmn: Result[Bpmn, Error] = Failure(
            NotInitializedError("PromelaBulider.bpmn")
        )
        self.cwp: Result[Cwp, Error] = Failure(
            NotInitializedError("PromelaBulider.cwp")
        )
        self.state: Result[State, Error] = Failure(
            NotInitializedError("PromelaBulider.state")
        )

    def build(self) -> Result[str, Error]:
        result: Result[str, Error] = self.state.bind(  # pyright: ignore[reportUnknownMemberType]
            lambda state: self.cwp.bind(  # pyright: ignore[reportUnknownMemberType]
                lambda cwp: self.bpmn.bind(  # pyright: ignore[reportUnknownMemberType]
                    lambda bpmn: _generate_promela(state, cwp, bpmn)
                )
            )
        )
        return result

    def with_bpmn(self, bpmn: Bpmn) -> "PromelaBuilder":
        self.bpmn = Success(bpmn)
        return self

    def with_cwp(self, cwp: Cwp) -> "PromelaBuilder":
        self.cwp = Success(cwp)
        return self

    def with_state(self, state: State) -> "PromelaBuilder":
        self.state = Success(state)
        return self


class Outputs:
    __slots__ = ["promela"]

    def __init__(self, promela: str) -> None:
        self.promela = promela
