from typing import List, Optional
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
from bpmncwpverify.util.stringmanager import StringManager, IndentAction

##############
# Constants
##############
HELPER_FUNCS_STR = "#define hasToken(place) (place != 0)\n\ninline putToken(place) {\n\tassert (place != 1)\n\tplace = 1\n}\n\n#define consumeToken(place) place = 0\n"
NL_NONE = 0
NL_SINGLE = 1
NL_DOUBLE = 2


##############


class Context:
    __slots__ = [
        "_element",
        "_task_end",
        "_is_parallel",
        "_behavior_model",
        "_has_option",
        "_behavior",
        "_end_event",
    ]

    def __init__(self, element: Node) -> None:
        self._element = element
        self._task_end = False
        self._is_parallel = False
        self._has_option = False
        self._behavior_model = True
        self._behavior = ""
        self._end_event = False

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
    def has_option(self) -> bool:
        return self._has_option

    @has_option.setter
    def has_option(self, new_val: bool) -> None:
        assert isinstance(self._element, ExclusiveGatewayNode)
        self._has_option = new_val

    @property
    def behavior_model(self) -> bool:
        return self._behavior_model

    @behavior_model.setter
    def behavior_model(self, new_val: bool) -> None:
        self._behavior_model = new_val

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
    def behavior(self) -> str:
        return self._behavior

    @behavior.setter
    def behavior(self, new_val: str) -> None:
        assert isinstance(
            self._element, Task
        ), "only tasks can have a behavior associated with them."
        self._behavior = new_val

    @property
    def end_event(self) -> bool:
        return self._end_event

    @end_event.setter
    def end_event(self, new_val: bool) -> None:
        assert isinstance(
            self._element, EndEvent
        ), "end_event can only be set if element is of type EndEvent"
        self._end_event = new_val

    @property
    def element(self) -> Node:
        return self._element


class PromelaGenVisitor(BpmnVisitor):  # type: ignore
    def __init__(self) -> None:
        self.defs = StringManager()
        self.var_defs = StringManager()
        self.behaviors = StringManager()
        self.init_proc_contents = StringManager()
        self.promela = StringManager()

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
            return f"{ctx.element.id}_FROM_{flow_or_message.source_node.id}"
        if ctx.task_end:
            return f"{ctx.element.id}_END"
        return ctx.element.id  # type: ignore

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
        sm = StringManager()
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
        guard = StringManager()
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

        atomic_block = StringManager()
        atomic_block.write_str(":: atomic { (")

        guard = self._build_guard(ctx)

        atomic_block.write_str(guard)
        atomic_block.write_str(") ->", NL_SINGLE, IndentAction.INC)
        if ctx.behavior_model:
            atomic_block.write_str(f"{ctx.element.id}_BehaviorModel()", NL_SINGLE)
        atomic_block.write_str("d_step {", NL_SINGLE, IndentAction.INC)

        for location in self._get_consume_locations(ctx):
            atomic_block.write_str(f"consumeToken({location})", NL_SINGLE)

        if ctx.has_option:
            atomic_block.write_str(self._build_expr_conditional(ctx))
        else:
            for location in self._get_put_locations(ctx):
                atomic_block.write_str(f"putToken({location})", NL_SINGLE)

        atomic_block.write_str("}", NL_SINGLE, IndentAction.DEC)

        if ctx.end_event:
            atomic_block.write_str("break", NL_SINGLE)

        atomic_block.write_str("}", NL_SINGLE, IndentAction.DEC)

        return atomic_block

    def _gen_behavior_model(self, ctx: Context) -> None:
        """
        Writes to the behaviors field to make an inline behavior model for the
        passed element.
        """
        self.behaviors.write_str(
            f"inline {ctx.element.id}_BehaviorModel(){{", NL_SINGLE, IndentAction.INC
        )
        if ctx.behavior:
            self.behaviors.write_str(ctx.behavior, NL_SINGLE)
        else:
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

        self.promela.write_str(f"putToken({event.id})", NL_SINGLE, IndentAction.NIL)
        self.promela.write_str("do", NL_SINGLE, IndentAction.NIL)

        atomic_block = self._build_atomic_block(context)

        self.promela.write_str(atomic_block)
        return True

    def visit_end_event(self, event: EndEvent) -> bool:
        context = Context(event)
        context.end_event = True
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
        context.behavior = task.behavior
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
        context.has_option = True
        context.behavior_model = False
        self._gen_var_defs(context)

        atomic_block = self._build_atomic_block(context)
        self.promela.write_str(atomic_block)
        return True

    def end_visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> None:
        pass

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        context = Context(gateway)
        context.behavior_model = False
        if not gateway.is_fork:
            context.is_parallel = True
        self._gen_var_defs(context)

        atomic_block = self._build_atomic_block(context)
        self.promela.write_str(atomic_block)
        return True

    def visit_message_flow(self, flow: MessageFlow) -> bool:
        return True

    def visit_process(self, process: Process) -> bool:
        self.init_proc_contents.write_str(
            f"run {process.id}()", NL_SINGLE, IndentAction.NIL
        )
        self.promela.write_str(
            f"proctype {process.id}() {{", NL_SINGLE, IndentAction.INC
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
