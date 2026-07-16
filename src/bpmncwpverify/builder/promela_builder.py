from returns.result import Failure, Result, Success

from bpmncwpverify.core.bpmn import Bpmn
from bpmncwpverify.core.cwp import Cwp
from bpmncwpverify.core.error import Error, NotInitializedError
from bpmncwpverify.core.state import State
from bpmncwpverify.core.typechecking import TYPEDEF
from bpmncwpverify.util.stringmanager import (
    NL_DOUBLE,
    NL_SINGLE,
    IndentAction,
    StringManager,
)
from bpmncwpverify.visitors.bpmn_promela_visitor import PromelaGenVisitor
from bpmncwpverify.visitors.cwp_promela_visitor import CwpPromelaVisitor

DEBUG_PROMELA = "#ifdef DEBUG\n#define DBG(x) x\n#else\n#define DBG(x)\n#endif\n\n"


def _generate_bpmn_promela(bpmn: Bpmn) -> str:
    promela_visitor = PromelaGenVisitor()
    bpmn.accept(promela_visitor)
    return str(promela_visitor)


def _generate_cwp_promela(cwp: Cwp, state: State) -> str:
    ltl_visitor = CwpPromelaVisitor()
    cwp.accept(ltl_visitor)
    return str(ltl_visitor)


def _generate_logger(state: State, cwp: Cwp) -> str:
    loggerFunction = StringManager()

    loggerFunction.write_str("inline stateLogger(){", NL_SINGLE, IndentAction.INC)
    loggerFunction.write_str('printf("Changed Vars: \\n")', NL_SINGLE)
    for path, var in state.str2var.items():
        if var.type_ == TYPEDEF:
            continue
        loggerFunction.write_str("if", NL_SINGLE, IndentAction.INC)
        loggerFunction.write_str(
            f":: {path} != old_{path} ->", NL_SINGLE, IndentAction.INC
        )
        loggerFunction.write_str(
            f'printf("{path} = {_get_print_type(var.type_)}\\n", {path})',
            NL_SINGLE,
        )
        loggerFunction.write_str(f"old_{path} = {path}", NL_SINGLE)
        loggerFunction.write_str(":: else", NL_SINGLE, IndentAction.DEC)
        loggerFunction.write_str("fi;", NL_SINGLE, IndentAction.DEC)

    for array in state.arrays:
        for i in range(len(array.values)):
            loggerFunction.write_str("if", NL_SINGLE, IndentAction.INC)
            loggerFunction.write_str(
                f":: {array.id}[{i}] != old_{array.id}[{i}] ->",
                NL_SINGLE,
                IndentAction.INC,
            )
            loggerFunction.write_str(
                f'printf("{array.id}[{i}] = {_get_print_type(array.type_)}\\n", {array.id}[{i}])',
                NL_SINGLE,
            )
            loggerFunction.write_str(
                f"old_{array.id}[{i}] = {array.id}[{i}]", NL_SINGLE
            )
            loggerFunction.write_str(":: else -> skip", NL_SINGLE, IndentAction.DEC)
            loggerFunction.write_str("fi;", NL_SINGLE, IndentAction.DEC)

    for array in state.arrays:
        for i in range(len(array.values)):
            loggerFunction.write_str("if", NL_SINGLE, IndentAction.INC)
            loggerFunction.write_str(
                f":: {array.id}[{i}] != old_{array.id}[{i}] ->",
                NL_SINGLE,
                IndentAction.INC,
            )
            loggerFunction.write_str(
                f'printf("{array.id}[{i}] = {_get_print_type(array.type_)}\\n", {array.id}[{i}])',
                NL_SINGLE,
            )
            loggerFunction.write_str(
                f"old_{array.id}[{i}] = {array.id}[{i}]", NL_SINGLE
            )
            loggerFunction.write_str(":: else -> skip", NL_SINGLE, IndentAction.DEC)
            loggerFunction.write_str("fi;", NL_SINGLE, IndentAction.DEC)

    for cwp_state in cwp.states.values():
        loggerFunction.write_str("if", NL_SINGLE, IndentAction.INC)
        loggerFunction.write_str(
            f":: {cwp_state.name} == true ->", NL_SINGLE, IndentAction.INC
        )
        loggerFunction.write_str(
            f'printf("Current state: {cwp_state.name}\\n")', NL_SINGLE
        )
        loggerFunction.write_str(":: else", NL_SINGLE, IndentAction.DEC)
        loggerFunction.write_str("fi;", NL_SINGLE, IndentAction.DEC)
    loggerFunction.write_str("}", NL_DOUBLE, IndentAction.DEC)
    return str(loggerFunction)


def _generate_state_dump(state: State) -> str:
    state_dump = StringManager()
    state_dump.write_str("inline stateDump(){", NL_SINGLE, IndentAction.INC)

    for path, var in state.str2var.items():
        if var.type_ != TYPEDEF:
            state_dump.write_str(
                f'printf("{path} = {_get_print_type(var.type_)}\\n", {path})', NL_SINGLE
            )

    for array in state.arrays:
        valTypeList: str = ""
        valDeclList: str = ""
        comma: str = ", "
        for i in range(len(array.values)):
            if i == len(array.values) - 1:
                comma = ""
            valTypeList += f"{_get_print_type(array.type_)}" + comma
            valDeclList += f"{array.id}[{i}]" + comma
        state_dump.write_str(
            f'printf("{array.id} = {{{valTypeList}}}", {valDeclList})', NL_SINGLE
        )

    state_dump.write_str("}", NL_DOUBLE, IndentAction.DEC)
    return str(state_dump)


def _generate_promela(state: State, cwp: Cwp, bpmn: Bpmn) -> Result[str, Error]:
    cwp_pml = _generate_cwp_promela(cwp, state)
    state_dump_pml = _generate_state_dump(state)
    logger_pml = _generate_logger(state, cwp)
    vars_pml = _generate_state_promela(state)
    bpmn_pml = _generate_bpmn_promela(bpmn)
    pml = f"{DEBUG_PROMELA}{vars_pml}{cwp_pml}{logger_pml}{state_dump_pml}{bpmn_pml}"
    return Success(pml)


def _generate_state_promela(state: State) -> str:
    str_builder: list[str] = []
    str_builder.append("//**********VARIABLE DECLARATION************//")
    for const_decl in state.consts:
        str_builder.append(f"#define {const_decl.id} {const_decl.init.value}")
    for enum_decl in state.enums:
        str_builder.append(
            f"mtype:{enum_decl.id} = {{{' '.join(sorted([value.value for value in enum_decl.values]))}}}"
        )
    for array_decl in state.arrays:
        arrayBuilder: str = (
            f"{array_decl.type_} {array_decl.id}[{array_decl.size}] = {{"
        )
        if "bit" not in array_decl.type_ and "bool" not in array_decl.type_:
            hiddenBuilder: str = (
                f"hidden {array_decl.type_} old_{array_decl.id}[{array_decl.size}] = {{"
            )
        else:
            hiddenBuilder = (
                f"{array_decl.type_} old_{array_decl.id}[{array_decl.size}] = {{"
            )

        index: int = 0
        comma: str = ", "
        for valDecl in array_decl.values:
            if index == len(array_decl.values) - 1:
                comma = ""
            arrayBuilder += f"{valDecl.value}{comma}"
            hiddenBuilder += f"{valDecl.value}{comma}"
            index += 1
        str_builder.append(arrayBuilder + "}")
        str_builder.append(hiddenBuilder + "}")
    # Generate typedefs
    for typedef_decl in state.typedefs:
        # Declare the typedef structure
        str_builder.append(f"typedef {typedef_decl.id} {{")
        for var_decl in typedef_decl.fields:
            if var_decl.type_ in {enum.id for enum in state.enums}:
                str_builder.append(f"    mtype:{var_decl.type_} {var_decl.id}")
            elif var_decl.type_ == TYPEDEF:
                str_builder.append(f"    {var_decl.init.value} {var_decl.id}")
            else:
                str_builder.append(f"    {var_decl.type_} {var_decl.id}")
        str_builder.append("}")
    # Generate variable declarations
    for var_decl in state.vars:
        if var_decl.type_ in {enum.id for enum in state.enums}:
            str_builder.append(
                f"mtype:{var_decl.type_} {var_decl.id} = {var_decl.init.value}"
            )
            if "bit" not in var_decl.type_:
                str_builder.append(
                    f"hidden mtype:{var_decl.type_} old_{var_decl.id} = {var_decl.id}"
                )
        elif var_decl.type_ == TYPEDEF:
            str_builder.append(f"{var_decl.init.value} {var_decl.id}")
            str_builder.append(f"{var_decl.init.value} old_{var_decl.id}")
        else:
            str_builder.append(
                f"{var_decl.type_} {var_decl.id} = {var_decl.init.value}"
            )

            if "bit" not in var_decl.type_ and "bool" not in var_decl.type_:
                str_builder.append(
                    f"hidden {var_decl.type_} old_{var_decl.id} = {var_decl.id}"
                )
            else:
                str_builder.append(
                    f"{var_decl.type_} old_{var_decl.id} = {var_decl.id}"
                )
    # Initialize each field in typedefs, if empty skip
    str_builder.append("inline typedefInit() {")
    if len(state.str2var) == 0 or len(state.typedefs) == 0:
        str_builder.append("    skip")
    else:
        str2var = state.str2var
        for path, var in str2var.items():
            if var.type_ == TYPEDEF:
                continue
            var = str2var[path]
            str_builder.append(f"    {path} = {var.init.value}")
            str_builder.append(f"    old_{path} = {var.init.value}")
    str_builder.append("}")

    return "\n".join(str_builder) + "\n\n"


def _get_print_type(type: str) -> str:
    match type:
        case "bit":
            return "%d"
        case "bool":
            return "%d"
        case "byte":
            return "%u"
        case "int":
            return "%d"
        case "short":
            return "%hd"
        case _:
            return "%e"


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
