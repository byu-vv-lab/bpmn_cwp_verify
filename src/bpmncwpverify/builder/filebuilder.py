from xml.etree.ElementTree import Element

from returns.unsafe import unsafe_perform_io
from returns.io import IOResultE
from returns.curry import partial
from returns.pipeline import flow, is_successful
from returns.pointfree import bind_result
from returns.result import Result, Success, Failure
from returns.functions import not_


from bpmncwpverify.core.error import Error, ExceptionError
from bpmncwpverify.core.state import State
from bpmncwpverify.core.cwp import Cwp
from bpmncwpverify.core.bpmn import Bpmn
from bpmncwpverify.core.accessmethods.bpmnmethods import (
    from_xml as bpmn_from_xml,
    generate_promela,
)
from bpmncwpverify.core.accessmethods.cwpmethods import (
    from_xml as cwp_from_xml,
)


class StateBuilder:
    __slots__ = [
        "behavior_str",
        "bpmn",
        "bpmn_root",
        "cwp",
        "cwp_root",
        "state_str",
        "state",
    ]

    def __init__(self) -> None:
        self.behavior_str: Result[str, Error] = Failure(Error())
        self.bpmn: Result[Bpmn, Error] = Failure(Error())
        self.bpmn_root: Result[Element, Error] = Failure(Error())
        self.cwp: Result[Cwp, Error] = Failure(Error())
        self.cwp_root: Result[Element, Error] = Failure(Error())
        self.state_str: Result[str, Error] = Failure(Error())
        self.state: Result[State, Error] = Failure(Error())

    @staticmethod
    def _build_bpmn(builder: "StateBuilder") -> Result["StateBuilder", Error]:
        assert is_successful(builder.state) and is_successful(builder.bpmn_root)
        builder.bpmn = bpmn_from_xml(builder.bpmn_root.unwrap(), builder.state.unwrap())
        if not_(is_successful)(builder.bpmn):
            return Failure(builder.bpmn.failure())
        else:
            return Success(builder)

    @staticmethod
    def _build_cwp(builder: "StateBuilder") -> Result["StateBuilder", Error]:
        assert is_successful(builder.state)
        assert is_successful(builder.cwp_root)
        builder.cwp = cwp_from_xml(builder.cwp_root.unwrap(), builder.state.unwrap())
        if not_(is_successful)(builder.cwp):
            return Failure(builder.cwp.failure())
        else:
            return Success(builder)

    @staticmethod
    def _build_state(builder: "StateBuilder") -> Result["StateBuilder", Error]:
        assert is_successful(builder.state_str)
        builder.state = State.from_str(builder.state_str.unwrap())
        if not_(is_successful)(builder.state):
            return Failure(builder.state.failure())
        else:
            return Success(builder)

    @staticmethod
    def build_promela(
        outputs: "Outputs", builder: "StateBuilder"
    ) -> Result["Outputs", Error]:
        assert is_successful(builder.state)
        assert is_successful(builder.cwp_root)
        assert is_successful(builder.bpmn_root)
        assert is_successful(builder.behavior_str)

        # ltl = generate_ltl((builder.cwp).unwrap(), (builder.state).unwrap())
        # behavior = (builder.behavior_str).unwrap()
        vars = State.generate_promela((builder.state).unwrap()).unwrap()
        workflow = generate_promela((builder.bpmn).unwrap())

        # outputs.promela = f"{vars}{ltl}{behavior}{workflow}"
        outputs.promela = f"{vars}{workflow}"
        return Success(outputs)

    def build(self) -> Result["Outputs", Error]:
        outputs: Outputs = Outputs("")
        result: Result["Outputs", Error] = flow(
            Success(self),
            bind_result(StateBuilder._build_state),
            bind_result(StateBuilder._build_cwp),
            bind_result(StateBuilder._build_bpmn),
            bind_result(partial(StateBuilder.build_promela, outputs)),
        )

        return result

    def with_behavior(self, behavior_str: str) -> "StateBuilder":
        self.behavior_str = Success(behavior_str)
        return self

    def with_bpmn(self, bpmn: Element) -> "StateBuilder":
        self.bpmn_root = Success(bpmn)
        return self

    def with_cwp(self, cwp: Element) -> "StateBuilder":
        self.cwp_root = Success(cwp)
        return self

    def with_state(self, state: str) -> "StateBuilder":
        self.state_str = Success(state)
        return self

    @staticmethod
    def build_(builder: "StateBuilder") -> Result["Outputs", Error | Exception]:
        return builder.build()

    @staticmethod
    def with_behavior_(
        behavior_str: IOResultE[str],
        builder_result: Result["StateBuilder", Error],
    ) -> Result["StateBuilder", Error]:
        if not_(is_successful)(builder_result):
            return builder_result
        if not_(is_successful)(behavior_str):
            error = unsafe_perform_io(behavior_str.failure())
            return Failure(ExceptionError(str(error)))

        bpmn = Success(unsafe_perform_io(behavior_str.unwrap()))
        builder = builder_result.unwrap()
        return bpmn.map(builder.with_behavior)

    @staticmethod
    def with_bpmn_(
        bpmn_root: IOResultE[Element],
        builder_result: Result["StateBuilder", Error],
    ) -> Result["StateBuilder", Error]:
        if not_(is_successful)(builder_result):
            return builder_result
        if not_(is_successful)(bpmn_root):
            error = unsafe_perform_io(bpmn_root.failure())
            return Failure(ExceptionError(str(error)))

        bpmn = Success(unsafe_perform_io(bpmn_root.unwrap()))
        builder = builder_result.unwrap()
        return bpmn.map(builder.with_bpmn)

    @staticmethod
    def with_cwp_(
        cwp_root: IOResultE[Element],
        builder_result: Result["StateBuilder", Error],
    ) -> Result["StateBuilder", Error]:
        if not_(is_successful)(builder_result):
            return builder_result
        if not_(is_successful)(cwp_root):
            error = unsafe_perform_io(cwp_root.failure())
            return Failure(ExceptionError(str(error)))

        cwp = Success(unsafe_perform_io(cwp_root.unwrap()))
        builder = builder_result.unwrap()
        return cwp.map(builder.with_cwp)

    @staticmethod
    def with_state_(
        state_str: IOResultE[str], builder_result: Result["StateBuilder", Error]
    ) -> Result["StateBuilder", Error]:
        if not_(is_successful)(builder_result):
            return builder_result
        if not_(is_successful)(state_str):
            error = unsafe_perform_io(state_str.failure())
            return Failure(ExceptionError(str(error)))

        builder = builder_result.unwrap()
        state = Success(unsafe_perform_io(state_str.unwrap()))
        return state.map(builder.with_state)


class Outputs:
    __slots__ = ["promela"]

    def __init__(self, promela: str) -> None:
        self.promela = promela
