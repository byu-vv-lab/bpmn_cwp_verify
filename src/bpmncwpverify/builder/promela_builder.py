from xml.etree.ElementTree import Element

from returns.pipeline import flow, is_successful
from returns.pointfree import bind_result
from returns.result import Result, Success, Failure
from returns.functions import not_

from bpmncwpverify.core.error import Error
from bpmncwpverify.core.state import State
from bpmncwpverify.core.cwp import Cwp
from bpmncwpverify.core.bpmn import Bpmn
from bpmncwpverify.core.accessmethods.bpmnmethods import (
    from_xml as bpmn_from_xml,
    generate_promela,
)
from bpmncwpverify.core.accessmethods.cwpmethods import (
    CwpXmlParser,
    generate_cwp_promela,
)
from bpmncwpverify.util.stringmanager import StringManager, NL_SINGLE, IndentAction


class PromelaBuilder:
    __slots__ = [
        "bpmn",
        "bpmn_root",
        "cwp",
        "cwp_root",
        "state_str",
        "state",
    ]

    def __init__(self) -> None:
        self.bpmn: Result[Bpmn, Error] = Failure(Error())
        self.bpmn_root: Result[Element, Error] = Failure(Error())
        self.cwp: Result[Cwp, Error] = Failure(Error())
        self.cwp_root: Result[Element, Error] = Failure(Error())
        self.state_str: Result[str, Error] = Failure(Error())
        self.state: Result[State, Error] = Failure(Error())

    @staticmethod
    def _build_bpmn(builder: "PromelaBuilder") -> Result["PromelaBuilder", Error]:
        assert is_successful(builder.state) and is_successful(builder.bpmn_root)
        builder.bpmn = bpmn_from_xml(builder.bpmn_root.unwrap(), builder.state.unwrap())
        if not_(is_successful)(builder.bpmn):
            return Failure(builder.bpmn.failure())
        else:
            return Success(builder)

    @staticmethod
    def _build_cwp(builder: "PromelaBuilder") -> Result["PromelaBuilder", Error]:
        assert is_successful(builder.state)
        assert is_successful(builder.cwp_root)
        builder.cwp = CwpXmlParser.from_xml(
            builder.cwp_root.unwrap(), builder.state.unwrap()
        )
        if not_(is_successful)(builder.cwp):
            return Failure(builder.cwp.failure())
        else:
            return Success(builder)

    @staticmethod
    def _build_state(builder: "PromelaBuilder") -> Result["PromelaBuilder", Error]:
        assert is_successful(builder.state_str)
        builder.state = State.from_str(builder.state_str.unwrap())
        if not_(is_successful)(builder.state):
            return Failure(builder.state.failure())
        else:
            return Success(builder)

    @staticmethod
    def build_promela(builder: "PromelaBuilder") -> Result[str, Error]:
        assert is_successful(builder.state)
        assert is_successful(builder.cwp_root)
        assert is_successful(builder.bpmn_root)

        cwp = generate_cwp_promela((builder.cwp).unwrap(), (builder.state).unwrap())
        vars = State.generate_promela((builder.state).unwrap()).unwrap()
        variableLogger = builder.logger_generator(
            (builder.state).unwrap(), (builder.cwp).unwrap()
        )
        workflow = generate_promela((builder.bpmn).unwrap())

        promela = f"{vars}{cwp}{variableLogger}{workflow}"
        return Success(promela)

    def logger_generator(self, state: State, cwp: Cwp) -> str:
        variableNames = self.variable_name_extractor(state)
        loggerFunction = StringManager()

        loggerFunction.write_str("inline stateLogger(){", NL_SINGLE, IndentAction.INC)
        loggerFunction.write_str('printf("Changed Vars: \\n");', NL_SINGLE)
        for varName in variableNames:
            loggerFunction.write_str("if", NL_SINGLE, IndentAction.INC)
            loggerFunction.write_str(
                f":: {varName} != old_{varName} ->", NL_SINGLE, IndentAction.INC
            )
            loggerFunction.write_str(
                f'printf("{varName} = %e\\n", {varName});', NL_SINGLE
            )
            loggerFunction.write_str(f"old_{varName} = {varName}", NL_SINGLE)
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

    def variable_name_extractor(self, state: State) -> list[str]:
        variableNames: list[str] = []
        for var in state.vars:
            variableNames.append(var.id)
        return variableNames

    def build(self) -> Result[str, Error]:
        result: Result[str, Error] = flow(
            Success(self),
            bind_result(PromelaBuilder._build_state),
            bind_result(PromelaBuilder._build_cwp),
            bind_result(PromelaBuilder._build_bpmn),
            bind_result(PromelaBuilder.build_promela),
        )

        return result

    def with_bpmn(self, bpmn: Element) -> "PromelaBuilder":
        self.bpmn_root = Success(bpmn)
        return self

    def with_cwp(self, cwp: Element) -> "PromelaBuilder":
        self.cwp_root = Success(cwp)
        return self

    def with_state(self, state: str) -> "PromelaBuilder":
        self.state_str = Success(state)
        return self

    @staticmethod
    def build_(builder: "PromelaBuilder") -> Result[str, Error]:
        return builder.build()

    @staticmethod
    def with_bpmn_(
        bpmn_root: Result[Element, Error],
        builder_result: Result["PromelaBuilder", Error],
    ) -> Result["PromelaBuilder", Error]:
        return builder_result.bind(  # pyright: ignore[reportUnknownMemberType]
            lambda builder: bpmn_root.map(lambda bpmn: builder.with_bpmn(bpmn))
        )

    @staticmethod
    def with_cwp_(
        cwp_root: Result[Element, Error],
        builder_result: Result["PromelaBuilder", Error],
    ) -> Result["PromelaBuilder", Error]:
        return builder_result.bind(  # pyright: ignore[reportUnknownMemberType]
            lambda builder: cwp_root.map(lambda cwp: builder.with_cwp(cwp))
        )

    @staticmethod
    def with_state_(
        state_str: Result[str, Error], builder_result: Result["PromelaBuilder", Error]
    ) -> Result["PromelaBuilder", Error]:
        return builder_result.bind(  # pyright: ignore[reportUnknownMemberType]
            lambda builder: state_str.map(lambda state: builder.with_state(state))
        )


class Outputs:
    __slots__ = ["promela"]

    def __init__(self, promela: str) -> None:
        self.promela = promela
