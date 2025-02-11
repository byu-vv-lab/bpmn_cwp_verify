from typing import List, Optional, Union
from enum import Enum
from bpmncwpverify.core.bpmn import (
    Flow,
    Node,
    StartEvent,
    EndEvent,
    IntermediateEvent,
    Task,
    MessageFlow,
    ParallelGatewayNode,
    ExclusiveGatewayNode,
    BpmnVisitor,
    Process,
    Bpmn,
)

##############
# Constants
##############
HELPER_FUNCS_STR = "\n\n#define hasToken(place) (place != 0)\n\n#define putToken(place) place = 1\n\n#define consumeToken(place) place = 0"
NL_NONE = 0
NL_SINGLE = 1
NL_DOUBLE = 2


##############
class IndentAction(Enum):
    NIL = 0
    INC = 1
    DEC = 2


class Context:
    __slots__ = ["_element", "_task_end", "_is_parallel"]

    def __init__(self, element: Node) -> None:
        self._element = element
        self._task_end = False
        self._is_parallel = False

    @property
    def task_end(self) -> bool:
        return self._task_end

    @task_end.setter
    def task_end(self, new_val: bool) -> None:
        assert isinstance(
            self._element, Task
        ), "task_end can only be set if element is of type Task"
        self._task_end = new_val

    @property
    def is_parallel(self) -> bool:
        return self._is_parallel

    @is_parallel.setter
    def is_parallel(self, new_val: bool) -> None:
        assert isinstance(
            self._element, ParallelGatewayNode
        ), "is_parallel can only be set if element is of type ParallelGatewayNode"
        self._is_parallel = new_val

    @property
    def element(self) -> Node:
        return self._element


class PromelaGenVisitor(BpmnVisitor):  # type: ignore
    class StringManager:
        def __init__(self) -> None:
            self.contents: List[str] = []
            self.indent = 0

        def _tab(self) -> str:
            """return string contianing 'self.indent' tabs"""
            return "\t" * self.indent

        def _newline(self, nl: int) -> str:
            """Return string containing 'nl' new lines."""
            return "\n" * nl

        def _inc_indent(self) -> None:
            self.indent += 1

        def _dec_indent(self) -> None:
            assert self.indent > 0
            self.indent -= 1

        def write_str(
            self,
            new_str: Union[str, "PromelaGenVisitor.StringManager"],
            nl: int = NL_NONE,
            indent_action: IndentAction = IndentAction.NIL,
        ) -> None:
            """
            Appends a string or the contents of a StringManager object to the internal contents list
            with specified newline and indentation behavior.
            """
            # Validate input for StringManager instance usage
            if isinstance(new_str, PromelaGenVisitor.StringManager):
                if nl != NL_NONE or indent_action != IndentAction.NIL:
                    raise ValueError(
                        "When passing a StringManager, nl must be NL_NONE and indent_action must be IndentAction.NIL"
                    )

            if indent_action == IndentAction.DEC:
                self._dec_indent()

            def needs_tab(idx: int, items: List[str]) -> bool:
                """Helper function to determine if tabulation is necessary."""
                # Check if it's the first item and if the last content line ends with a newline
                if idx == 0:
                    return bool(self.contents and self.contents[-1].endswith("\n"))
                # Check the previous item for a newline
                return items[idx - 1].endswith("\n")

            # Normalize the input into a list for consistent handling
            items = [new_str] if isinstance(new_str, str) else new_str.contents

            for idx, item in enumerate(items):
                tab_required = needs_tab(idx, items)
                newline_suffix = self._newline(nl) if isinstance(new_str, str) else ""
                self.contents.append(
                    f"{self._tab() if tab_required else ''}{item}{newline_suffix}"
                )

            if indent_action == IndentAction.INC:
                self._inc_indent()

        def __repr__(self) -> str:
            return "".join(self.contents)

    def __init__(self) -> None:
        self.defs = PromelaGenVisitor.StringManager()
        self.var_defs = PromelaGenVisitor.StringManager()
        self.behaviors = PromelaGenVisitor.StringManager()
        self.init_proc_contents = PromelaGenVisitor.StringManager()
        self.promela = PromelaGenVisitor.StringManager()

    def _generate_location_label(
        self, ctx: Context, flow_or_message: Optional[Flow] = None
    ) -> str:
        """
        Should only be called from _get_consume_locations and _get_put_locations.
        Generates a unique label for a node, indicating the source of flow.
        If multiple flows lead into the node, the label specifies the source element
        (e.g., 'Node1_FROM_Start'). If the node is a Task, the label ends with '_END'.
        """
        if flow_or_message:
            return f"{ctx.element.name}_FROM_{flow_or_message.source_node.name}"
        if ctx.task_end:
            return f"{ctx.element.name}_END"
        return ctx.element.name  # type: ignore

    def _get_consume_locations(self, ctx: Context) -> List[str]:
        """
        Returns a list of labels representing all incoming flows to a node.
        If there are no incoming flows, the node itself is returned as a label.
        Example: ['Node2_FROM_Start', 'Node2_FROM_Node1']
        """
        if not (ctx.element.in_flows or ctx.element.in_msgs) or ctx.task_end:
            return [self._generate_location_label(ctx)]
        return [
            self._generate_location_label(ctx, flow)
            for flow in ctx.element.in_flows + ctx.element.in_msgs
        ]

    def _get_expressions(self, ctx: Context) -> List[str]:
        """
        Returns a list of the expressions that lie on the flows leaving a specific
        node. Example: ["x > 5"]
        """
        return [flow.expression for flow in ctx.element.out_flows if flow.expression]

    def _build_expr_conditional(self, ctx: Context) -> StringManager:
        """
        This function builds and returns a conditional block. This should be called
        only by the _build_atomic_block function.
        example:
        if
            :: x > 5 -> putToken(...)
            :: ...
        fi
        """
        sm = PromelaGenVisitor.StringManager()
        sm.write_str("if", NL_SINGLE, IndentAction.INC)
        # This zip works because the out_flows is an array, which holds its order
        for expression, location in zip(
            self._get_expressions(ctx), self._get_put_locations(ctx)
        ):
            sm.write_str(f":: {expression} -> putToken({location})", NL_SINGLE)

        sm.write_str(":: atomic{else -> assert false}", NL_SINGLE)
        sm.write_str("fi", NL_SINGLE, IndentAction.DEC)
        return sm

    def _get_put_locations(self, ctx: Context) -> List[str]:
        """
        Returns a list of labels representing all outgoing flows from a node.
        Each label indicates the target node and the current node as the source.
        Example: ['Node2_FROM_Node1']
        """
        if ctx.task_end:
            return [self._generate_location_label(ctx)]
        else:
            return [
                self._generate_location_label(Context(flow.target_node), flow)
                for flow in ctx.element.out_flows + ctx.element.out_msgs
            ]

    def _build_guard(self, ctx: Context) -> StringManager:
        """
        Constructs a guard condition for an atomic block in a process.
        The guard checks whether a token exists at the current node, based on incoming flows.
        Example: (hasToken(Node2_FROM_Start) || hasToken(Node2_FROM_Node1))
        """
        guard = PromelaGenVisitor.StringManager()
        guard.write_str("(")
        if ctx.is_parallel:
            guard.write_str(
                " && ".join(
                    [f"hasToken({loc})" for loc in self._get_consume_locations(ctx)]
                )
            )
        else:
            guard.write_str(
                " || ".join(
                    [f"hasToken({node})" for node in self._get_consume_locations(ctx)]
                )
            )
        guard.write_str(")")
        return guard

    def _build_atomic_block(self, ctx: Context) -> StringManager:
        """
        This function builds an atomic block to execute the element's behavior,
        consume the token and move the token forward.
        """

        atomic_block = PromelaGenVisitor.StringManager()
        atomic_block.write_str(":: atomic { (")

        guard = self._build_guard(ctx)

        atomic_block.write_str(guard)
        atomic_block.write_str(") ->", NL_SINGLE, IndentAction.INC)
        atomic_block.write_str(f"{ctx.element.name}_BehaviorModel()", NL_SINGLE)
        atomic_block.write_str("d_step {", NL_SINGLE, IndentAction.INC)

        for location in self._get_consume_locations(ctx):
            atomic_block.write_str(f"consumeToken({location})", NL_SINGLE)

        else:
            for location in self._get_put_locations(ctx):
                atomic_block.write_str(f"putToken({location})", NL_SINGLE)

        atomic_block.write_str("}", NL_SINGLE, IndentAction.DEC)
        atomic_block.write_str("}", NL_SINGLE, IndentAction.DEC)

        return atomic_block

    def _gen_behavior_model(self, ctx: Context) -> None:
        """
        Writes to the behaviors field to make an inline behavior model for the
        passed element.
        """
        self.behaviors.write_str(
            f"inline {ctx.element.name}_BehaviorModel(){{", NL_SINGLE, IndentAction.INC
        )
        self.behaviors.write_str("skip", NL_SINGLE)
        self.behaviors.write_str("}", NL_DOUBLE, IndentAction.DEC)

    def _gen_var_defs(self, ctx: Context) -> None:
        for var in self._get_consume_locations(ctx):
            self.var_defs.write_str(f"bit {var} = 0", NL_SINGLE)

    def __repr__(self) -> str:
        return f"{self.defs}{self.var_defs}{self.behaviors}{self.init_proc_contents}{self.promela}"

    ####################
    # Visitor Methods
    ####################
    def visit_start_event(self, event: StartEvent) -> bool:
        context = Context(event)
        self._gen_behavior_model(context)
        self._gen_var_defs(context)

        self.promela.write_str(f"putToken({event.name})", NL_SINGLE, IndentAction.NIL)
        self.promela.write_str("do", NL_SINGLE, IndentAction.NIL)

        atomic_block = self._build_atomic_block(context)

        self.promela.write_str(atomic_block)
        return True

    def visit_end_event(self, event: EndEvent) -> bool:
        context = Context(event)
        self._gen_behavior_model(context)
        self._gen_var_defs(context)

        atomic_block = self._build_atomic_block(context)

        self.promela.write_str(atomic_block)
        return True

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        context = Context(event)
        self._gen_behavior_model(context)
        self._gen_var_defs(context)

        atomic_block = self._build_atomic_block(context)

        self.promela.write_str(atomic_block)
        return True

    def visit_task(self, task: Task) -> bool:
        context = Context(task)
        context.task_end = False
        self._gen_behavior_model(context)
        self._gen_var_defs(context)

        atomic_block = self._build_atomic_block(context)

        self.promela.write_str(atomic_block)
        return True

    def end_visit_task(self, task: Task) -> None:
        context = Context(task)
        context.task_end = True
        self._gen_var_defs(context)

        atomic_block = self._build_atomic_block(context)
        self.promela.write_str(atomic_block)

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        context = Context(gateway)
        self._gen_behavior_model(context)
        self._gen_var_defs(context)

        atomic_block = self._build_atomic_block(context)
        self.promela.write_str(atomic_block)
        return True

    def end_visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        context = Context(gateway)
        if not gateway.is_fork:
            context.is_parallel = True
        self._gen_behavior_model(context)
        self._gen_var_defs(context)

        atomic_block = self._build_atomic_block(context)

        self.promela.write_str(atomic_block)
        return True

    def visit_message_flow(self, flow: MessageFlow) -> bool:
        return True

    def visit_process(self, process: Process) -> bool:
        self.init_proc_contents.write_str(
            f"run {process.name}()", NL_SINGLE, IndentAction.NIL
        )
        self.promela.write_str(
            f"proctype {process.name}() {{", NL_SINGLE, IndentAction.INC
        )
        self.promela.write_str("pid me = _pid", NL_SINGLE, IndentAction.NIL)
        return True

    def end_visit_process(self, process: Process) -> None:
        self.promela.write_str("od", NL_SINGLE)
        self.promela.write_str("}", NL_SINGLE, IndentAction.DEC)

    def visit_bpmn(self, bpmn: Bpmn) -> bool:
        self.defs.write_str(HELPER_FUNCS_STR, NL_DOUBLE)
        self.init_proc_contents.write_str("init {", NL_SINGLE, IndentAction.INC)
        return True

    def end_visit_bpmn(self, bpmn: Bpmn) -> None:
        self.init_proc_contents.write_str("}", NL_DOUBLE, IndentAction.DEC)
