from bpmncwpverify.core.bpmn import (
    Bpmn,
    BpmnVisitor,
    EndEvent,
    EventBasedGatewayNode,
    ExclusiveGatewayNode,
    Flow,
    IntermediateEvent,
    MessageFlow,
    Node,
    ParallelGatewayNode,
    Process,
    StartEvent,
    Task,
)
from bpmncwpverify.core.feel import Feel
from bpmncwpverify.util.stringmanager import IndentAction, StringManager
from bpmncwpverify.visitors.feel_to_promela_visitor import FeelToPromelaVisitor

##############
# Constants
##############
HELPER_FUNCS_STR = '#define sendToken(place) place = 1\n#define receiveToken(place) place = 0\n#define hasToken(place) (place != 0)\n\ninline putToken(place) {\n\tif\n\t\t:: place == 0 ->\n\t\t\tplace = 1\n\t\t:: else -> \n\t\t\tDBG(printf("Assert: Attempting to place token in already-occupied place\\n"))\n\t\t\tassert(false)\n\tfi\n}\n\n#define consumeToken(place) place = 0'
NL_NONE = 0
NL_SINGLE = 1
NL_DOUBLE = 2


##############


class Context:
    __slots__ = [
        "_element",
        "_is_parallel",
        "_behavior",
        "_boundary_events",
    ]

    def __init__(self, element: Node) -> None:
        self._element = element
        self._is_parallel = False
        self._behavior: Feel | None = None
        self._boundary_events: list[Task.BoundaryEvent] = []

    @property
    def is_parallel(self) -> bool:
        return self._is_parallel

    @is_parallel.setter
    def is_parallel(self, new_val: bool) -> None:
        assert isinstance(self._element, ParallelGatewayNode), (
            "is_parallel can only be set if element is of type ParallelGatewayNode"
        )
        self._is_parallel = new_val

    @property
    def behavior(self) -> Feel | None:
        return self._behavior

    @behavior.setter
    def behavior(self, new_val: Feel) -> None:
        assert isinstance(self._element, Task), (
            "only tasks can have a behavior associated with them."
        )
        self._behavior = new_val

    @property
    def boundary_events(self) -> list[Task.BoundaryEvent]:
        return self._boundary_events

    @boundary_events.setter
    def boundary_events(self, new_val: list[Task.BoundaryEvent]) -> None:
        assert isinstance(self._element, Task), (
            "Only allowed to set boundary_events on a task."
        )
        self._boundary_events = new_val

    @property
    def element(self) -> Node:
        return self._element


class TokenPositions:
    """
    This class is simply a way to separate out the sequence flows and the message
    flows so that when building the guard in the atomic block, we can make
    sure that the triggerable event has a token from one of its incoming sequence
    flows and one of its incoming message flows.
    """

    __slots__ = ["seq_flows", "msg_flows", "standalone"]

    def __init__(
        self,
        seq_flows: list[str] | None = None,
        msg_flows: list[str] | None = None,
        standalone: str = "",
    ) -> None:
        self.seq_flows = seq_flows if seq_flows is not None else []
        self.msg_flows = msg_flows if msg_flows is not None else []
        self.standalone = standalone

        # Ensure that either seq/msg flows are provided or a standalone position, but not both.
        if (self.seq_flows or self.msg_flows) and self.standalone:
            raise ValueError(
                "Cannot have both sequence/message flows and a standalone position."
            )
        if not ((self.seq_flows or self.msg_flows) or self.standalone):
            raise ValueError(
                "Either sequence/message flows or a standalone position must be provided."
            )

    def get_all_positions(self) -> list[str]:
        return (
            self.seq_flows + self.msg_flows
            if (self.seq_flows or self.msg_flows)
            else [self.standalone]
        )

    def get_in_process_positions(self) -> list[str]:
        if self.seq_flows:
            return self.seq_flows
        elif self.standalone:
            return [self.standalone]
        else:
            return []


def generate_location_label(element: Node, flow_or_message: Flow | None = None) -> str:
    """
    Should only be called from _get_consume_locations and _get_put_locations.   REMOVE THIS LINE IF NOT TRUE
    Generates a unique label for a node, indicating the source of flow.
    If multiple flows lead into the node, the label specifies the source element
    (e.g., 'Node1_FROM_Start'). If the node is a Task, the label ends with '_END'.
    """
    if flow_or_message:
        return f"{element.id}_FROM_{flow_or_message.source_node.id}"
    return element.id


def get_consume_locations(element: Node) -> "TokenPositions":
    """
    Returns a list of labels representing all incoming flows to a node.
    If there are no incoming flows, the node itself is returned as a label.
    Example: ['Node2_FROM_Start', 'Node2_FROM_Node1']
    """
    if not (element.in_flows or element.in_msgs):
        return TokenPositions(standalone=generate_location_label(element))
    return TokenPositions(
        seq_flows=[generate_location_label(element, flow) for flow in element.in_flows],
        msg_flows=[generate_location_label(element, flow) for flow in element.in_msgs],
    )


def get_put_locations(element: Node) -> TokenPositions:
    """
    Returns a list of labels representing all outgoing flows from a node.
    Each label indicates the target node and the current node as the source.
    Example: ['Node2_FROM_Node1']
    """
    if not (element.out_flows or element.out_msgs):
        return TokenPositions(standalone=generate_location_label(element))
    return TokenPositions(
        seq_flows=[
            generate_location_label(flow.target_node, flow)
            for flow in element.out_flows
        ],
        msg_flows=[
            generate_location_label(flow.target_node, flow) for flow in element.out_msgs
        ],
    )


class PromelaGenVisitor(BpmnVisitor):
    __slots__ = [
        "defs",
        "process",
        "local_var_defs",
        "local_chooseschooses",
        "global_var_defs",
        "behaviors",
        "init_proc_contents",
        "promela",
    ]

    def __init__(self) -> None:
        self.defs = StringManager()
        self.process = StringManager()
        self.chooses = StringManager()
        self.local_var_defs = StringManager()
        self.local_chooses = StringManager()
        self.global_var_defs = StringManager()
        self.behaviors = StringManager()
        self.init_proc_contents = StringManager()
        self.promela = StringManager()

    def gen_var_defs(self, ctx: Context) -> None:
        locations = get_consume_locations(ctx.element)

        if not locations.standalone:
            for var in locations.msg_flows:
                self.global_var_defs.write_str(f"bit {var} = 0", NL_SINGLE)
            for var in locations.seq_flows:
                self.local_var_defs.write_str(f"bit {var} = 0", NL_SINGLE)
        else:
            self.local_var_defs.write_str(f"bit {locations.standalone} = 0", NL_SINGLE)

    def __repr__(self) -> str:
        return f"{self.defs}{self.global_var_defs}{self.behaviors}{self.init_proc_contents}{self.promela}"

    ####################
    # Visitor Methods
    ####################

    def visit_start_event(self, event: StartEvent) -> bool:
        context = Context(event)
        builder = StartEventBuilder(context)

        behavior, choose = builder.gen_behavior_model()
        self.behaviors.write_str(behavior)
        self.gen_var_defs(context)
        self.local_chooses.write_str(choose)

        flows = get_consume_locations(event)
        self.process.write_str(
            builder.out_seq_and_msg_flows(flows), indent_action=IndentAction.INC
        )

        # Close the d_step from the `visit_process`
        self.process.write_str("}", NL_SINGLE)
        self.process.write_str("do", NL_SINGLE)

        self.process.write_str(builder.build_atomic_block(), indent_offset=1)

        return True

    def visit_end_event(self, event: EndEvent) -> bool:
        context = Context(event)
        builder = EndEventBuilder(context)

        behavior, choose = builder.gen_behavior_model()
        self.behaviors.write_str(behavior)
        self.gen_var_defs(context)
        self.local_chooses.write_str(choose)

        self.process.write_str(builder.build_atomic_block(), indent_offset=1)

        return True

    def visit_intermediate_event(self, event: IntermediateEvent) -> bool:
        context = Context(event)
        builder = IntermediateEventBuilder(context)

        behavior, choose = builder.gen_behavior_model()
        self.behaviors.write_str(behavior)
        self.gen_var_defs(context)
        self.local_chooses.write_str(choose)

        self.process.write_str(builder.build_atomic_block(), indent_offset=1)

        return True

    def visit_task(self, task: Task) -> bool:
        context = Context(task)
        context.behavior = task.behavior
        context.boundary_events = task.msg_boundary_events
        builder = TaskBuilder(context)

        behavior, choose = builder.gen_behavior_model()
        self.behaviors.write_str(behavior)
        self.gen_var_defs(context)
        self.local_chooses.write_str(choose)

        self.process.write_str(builder.build_atomic_block(), indent_offset=1)

        return True

    def visit_event_based_gateway(self, gateway: EventBasedGatewayNode) -> bool:
        context = Context(gateway)
        builder = EventBasedGatewayBuilder(context)

        self.gen_var_defs(context)

        self.process.write_str(builder.build_atomic_block(), indent_offset=1)

        return True

    def visit_exclusive_gateway(self, gateway: ExclusiveGatewayNode) -> bool:
        context = Context(gateway)
        builder = ExclusiveGatewayBuilder(context)

        self.gen_var_defs(context)

        self.process.write_str(builder.build_atomic_block(), indent_offset=1)

        return True

    def visit_parallel_gateway(self, gateway: ParallelGatewayNode) -> bool:
        context = Context(gateway)
        builder = ParallelGatewayBuilder(context)

        if not gateway.is_fork:
            context.is_parallel = True

        self.gen_var_defs(context)

        self.process.write_str(builder.build_atomic_block(), indent_offset=1)

        return True

    def visit_message_flow(self, flow: MessageFlow) -> bool:
        return True

    def visit_process(self, process: Process) -> bool:
        self.process = StringManager()
        self.local_var_defs = StringManager()
        self.local_chooses = StringManager()

        self.init_proc_contents.write_str(
            f"run {process.id}()", NL_SINGLE, IndentAction.NIL
        )
        self.promela.write_str(
            f"proctype {process.id}() {{", NL_SINGLE, IndentAction.INC
        )
        return True

    def end_visit_process(self, process: Process) -> None:
        self.promela.write_str(self.local_var_defs, indent_offset=1)
        self.promela.write_str("", NL_SINGLE)

        self.promela.write_str(self.local_chooses, indent_offset=1)
        self.promela.write_str("", NL_SINGLE)

        self.promela.write_str("d_step {", NL_SINGLE, IndentAction.INC)
        self.promela.write_str(f'DBG(printf("ID: {process.id}\\n"))', NL_SINGLE)
        self.promela.write_str("DBG(stateLogger())", NL_SINGLE)
        self.promela.write_str("pid me = _pid", NL_SINGLE, IndentAction.NIL)

        self.promela.write_str(f"{self.process}")

        self.promela.write_str("od", NL_SINGLE, IndentAction.DEC)
        self.promela.write_str("}", NL_SINGLE, IndentAction.DEC)

    def visit_bpmn(self, bpmn: Bpmn) -> bool:
        self.defs.write_str(HELPER_FUNCS_STR, NL_DOUBLE)
        self.init_proc_contents.write_str("init {", NL_SINGLE, IndentAction.INC)
        self.init_proc_contents.write_str("atomic {", NL_SINGLE, IndentAction.INC)
        self.init_proc_contents.write_str("typedefInit()", NL_SINGLE)
        self.init_proc_contents.write_str("DBG(stateDump())", NL_SINGLE)
        self.init_proc_contents.write_str("caculateState()", NL_SINGLE)
        self.init_proc_contents.write_str("updateState()", NL_SINGLE)
        return True

    def end_visit_bpmn(self, bpmn: Bpmn) -> None:
        self.chooses.write_str("", NL_SINGLE)
        self.init_proc_contents.write_str("}", NL_SINGLE, IndentAction.DEC)
        self.init_proc_contents.write_str("}", NL_DOUBLE, IndentAction.DEC)


class AtomicBuilder:
    __slots__ = ["context"]

    def __init__(self, context: Context):
        self.context = context

    def out_seq_and_msg_flows(self, flows: TokenPositions) -> StringManager:
        outgoing = StringManager()

        if flows.standalone:
            outgoing.write_str(
                f"putToken({flows.standalone})", NL_SINGLE, IndentAction.INC
            )
        else:
            for loc in flows.seq_flows:
                outgoing.write_str(f"putToken({loc})", NL_SINGLE, IndentAction.NIL)
            for loc in flows.msg_flows:
                outgoing.write_str(f"sendToken({loc})", NL_SINGLE, IndentAction.NIL)

        return outgoing

    def in_seq_and_msg_flows(self, flows: TokenPositions) -> StringManager:
        in_going = StringManager()

        if flows.standalone:
            in_going.write_str(f"consumeToken({flows.standalone})", NL_SINGLE)
        else:
            for loc in flows.seq_flows:
                in_going.write_str(f"consumeToken({loc})", NL_SINGLE, IndentAction.NIL)
            for loc in flows.msg_flows:
                in_going.write_str(f"receiveToken({loc})", NL_SINGLE, IndentAction.NIL)

        return in_going

    def build_atomic_block(self) -> StringManager:
        """
        This function builds an atomic block to execute the element's behavior,
        consume the token and move the token forward.
        """
        atomic = StringManager()
        atomic.write_str(":: atomic { (")

        in_locations = get_consume_locations(self.context.element)
        out_locations = get_put_locations(self.context.element)

        atomic.write_str(self.build_guard(in_locations))

        atomic.write_str(self.add_structures(), indent_offset=1)

        atomic.write_str(self.add_in_flows(in_locations), indent_offset=2)

        atomic.write_str(self.add_out_flows(out_locations), indent_offset=2)

        atomic.write_str(self.add_end(), indent_offset=1)

        atomic.write_str("}", NL_SINGLE)

        return atomic

    def add_out_flows(self, out_locations: TokenPositions) -> StringManager:
        out_going = StringManager()

        out_going.write_str(self.out_seq_and_msg_flows(out_locations))

        return out_going

    def add_end(self) -> StringManager:
        end = StringManager()
        end.write_str("}", NL_SINGLE)

        return end

    def add_in_flows(self, in_locations: TokenPositions) -> StringManager:
        consumption = StringManager()

        consumption.write_str(self.in_seq_and_msg_flows(in_locations))

        return consumption

    def build_guard(self, in_locations: TokenPositions) -> StringManager:
        guard = StringManager()

        if seq_locs := in_locations.get_in_process_positions():
            guard.write_str("(")
            tokens: list[str] = [f"hasToken({pos})" for pos in seq_locs]
            guard.write_str(" || ".join(tokens))
            guard.write_str(")")

        if msg_locs := in_locations.msg_flows:
            guard.write_str(" && (" if seq_locs else "(")
            tokens_msg: list[str] = [f"{pos}" for pos in msg_locs]
            guard.write_str(" && ".join(tokens_msg))
            guard.write_str(")")

        guard.write_str(") ->", NL_SINGLE, IndentAction.INC)

        return guard

    def add_structures(
        self,
    ) -> StringManager:
        structure = StringManager()
        structure.write_str(
            f'DBG(printf("ID: {self.context.element.id}\\n"))', NL_SINGLE
        )
        if self.context.behavior:
            structure.write_str(f"{self.context.element.id}_BehaviorModel()", NL_SINGLE)

        structure.write_str("d_step {", NL_SINGLE, IndentAction.INC)

        structure.write_str("DBG(stateLogger())", NL_SINGLE)
        return structure

    def gen_behavior_model(self) -> tuple[StringManager, StringManager]:
        """
        Writes to the behaviors field to make an inline behavior model for the
        passed element.
        """
        behavior = StringManager()
        chooses = StringManager()
        selects = StringManager()

        if self.context.behavior:
            source_changer = FeelToPromelaVisitor(self.context.element.id)
            self.context.behavior.ast.accept(source_changer)
            behavior_source = str(source_changer.promela)
            chooses.write_str(source_changer.choose)
            selects.write_str(source_changer.selects)

            start_block_key_words = {"if"}
            end_block_key_words = {"fi"}
            behavior.write_str(
                f"inline {self.context.element.id}_BehaviorModel() {{",
                NL_SINGLE,
                IndentAction.INC,
            )
            behavior.write_str(selects, indent_offset=1)
            processed_str_list = [
                line.strip() for line in behavior_source.split("\n") if line.strip()
            ]

            for line in processed_str_list:
                if line in start_block_key_words:
                    behavior.write_str(line, NL_SINGLE, IndentAction.INC)
                elif line in end_block_key_words:
                    behavior.write_str(line, NL_SINGLE, IndentAction.DEC)
                else:
                    behavior.write_str(line, NL_SINGLE)

            behavior.write_str("updateState()", NL_SINGLE)

            behavior.write_str("}", NL_DOUBLE, IndentAction.DEC)

        return behavior, chooses


class StartEventBuilder(AtomicBuilder):
    pass


class EndEventBuilder(AtomicBuilder):
    def add_end(self) -> StringManager:
        end = StringManager()

        end.write_str("}", NL_SINGLE, IndentAction.NIL)
        end.write_str("break", NL_SINGLE)

        return end

    def add_out_flows(self, out_locations: TokenPositions) -> StringManager:
        out_going = StringManager()

        return out_going


class IntermediateEventBuilder(AtomicBuilder):
    def add_in_flows(self, in_locations: TokenPositions) -> StringManager:
        consumption = StringManager()

        if isinstance(
            self.context.element.in_flows[0].source_node, EventBasedGatewayNode
        ):
            gate = self.context.element.in_flows[0].source_node
            gate_out_tokens = get_put_locations(gate)
            consumption.write_str(self.in_seq_and_msg_flows(gate_out_tokens))

            for msg_other_tokens in gate.out_flows:
                token = get_consume_locations(msg_other_tokens.target_node)
                for loc in token.msg_flows:
                    consumption.write_str(
                        f"receiveToken({loc})", NL_SINGLE, IndentAction.NIL
                    )
        else:
            consumption.write_str(self.in_seq_and_msg_flows(in_locations))

        return consumption


class TaskBuilder(AtomicBuilder):
    def add_out_flows(self, out_locations: TokenPositions) -> StringManager:
        out_going = StringManager()

        if self.context.boundary_events:
            out_going.write_str(self.build_expression_conditional(out_locations))
        else:
            out_going.write_str(self.out_seq_and_msg_flows(out_locations))

        return out_going

    def build_expression_conditional(
        self, out_locations: TokenPositions
    ) -> StringManager:
        expr = StringManager()

        expr.write_str("if", NL_SINGLE)

        put_locations = [
            get_put_locations(boundary_event)
            for boundary_event in self.context.boundary_events
        ]
        in_locations = [
            get_consume_locations(boundary_event)
            for boundary_event in self.context.boundary_events
        ]

        for put_locs, in_locs in zip(put_locations, in_locations):
            expr.write_str(":: (")

            expr.write_str(
                " || ".join(
                    [f"hasToken({in_loc})" for in_loc in in_locs.seq_flows]
                    + [f"{in_loc}" for in_loc in in_locs.msg_flows]
                )
            )
            expr.write_str(") ->", NL_SINGLE, IndentAction.INC)
            expr.write_str(self.in_seq_and_msg_flows(in_locs), indent_offset=1)
            expr.write_str(self.out_seq_and_msg_flows(put_locs), indent_offset=1)

        expr.write_str(":: else ->", NL_SINGLE, IndentAction.INC)
        expr.write_str('DBG(printf("Assert: No viable path to take"))', NL_SINGLE)
        expr.write_str("assert(false)", NL_SINGLE)
        expr.write_str("fi", NL_SINGLE, IndentAction.DEC)

        return expr

    def build_guard(self, in_locations: TokenPositions) -> StringManager:
        guard = StringManager()

        if seq_locs := in_locations.get_in_process_positions():
            guard.write_str("(")
            tokens: list[str] = [f"hasToken({pos})" for pos in seq_locs]
            guard.write_str(" || ".join(tokens))

        if msg_locs := in_locations.msg_flows:
            guard.write_str(" && (" if seq_locs else "(")
            tokens_msg: list[str] = [f"{pos}" for pos in msg_locs]
            guard.write_str(" && ".join(tokens_msg))
            guard.write_str(")")

        guard.write_str(")")

        guards: list[str] = []
        for boundary_event in self.context.boundary_events:
            in_locs = get_consume_locations(boundary_event)
            if in_locs.standalone:
                guards.append(f" hasToken({in_locs.standalone})")
            else:
                guards.append(
                    " || ".join(
                        [f"hasToken({loc})" for loc in in_locs.seq_flows]
                        + [f"{loc}" for loc in in_locs.msg_flows]
                    )
                )

        if guards:
            guard.write_str(" && (")
        guard.write_str(" || ".join(guards))

        guard.write_str(") ->", NL_SINGLE, IndentAction.INC)

        return guard


class EventBasedGatewayBuilder(AtomicBuilder):
    def add_in_flows(self, in_locations: TokenPositions) -> StringManager:
        consumption = StringManager()

        consumption.write_str(self.in_seq_and_msg_flows(in_locations))

        return consumption


class ExclusiveGatewayBuilder(AtomicBuilder):
    def add_out_flows(self, out_locations: TokenPositions) -> StringManager:
        out_going = StringManager()

        out_going.write_str(self.build_expression_conditional(out_locations))

        return out_going

    def build_expression_conditional(
        self, out_locations: TokenPositions
    ) -> StringManager:
        expr = StringManager()

        expr.write_str("if", NL_SINGLE)

        for flow in self.context.element.out_flows:
            source_changer = FeelToPromelaVisitor(flow.id)
            flow.expression.ast.accept(source_changer)
            flow_expression = str(source_changer.promela)

            expr.write_str(
                f":: {flow_expression} -> putToken({generate_location_label(flow.target_node, flow)})",
                NL_SINGLE,
            )

        expr.write_str(":: else ->", NL_SINGLE, IndentAction.INC)
        expr.write_str('DBG(printf("Assert: No viable path to take"))', NL_SINGLE)
        expr.write_str("assert(false)", NL_SINGLE)
        expr.write_str("fi", NL_SINGLE, IndentAction.DEC)

        return expr


class ParallelGatewayBuilder(AtomicBuilder):
    def build_guard(
        self, in_locations: TokenPositions
    ) -> StringManager:  # will this ever be not paralell?
        guard = StringManager()

        if seq_locs := in_locations.get_in_process_positions():
            guard.write_str("(")
            tokens: list[str] = [f"hasToken({pos})" for pos in seq_locs]
            if self.context.is_parallel:
                guard.write_str(" && ".join(tokens))
            else:
                guard.write_str(" || ".join(tokens))

        if msg_locs := in_locations.msg_flows:
            guard.write_str(" && (" if seq_locs else "(")
            tokens_msg: list[str] = [f"{pos}" for pos in msg_locs]
            guard.write_str(" && ".join(tokens_msg))
            guard.write_str(")")

        guard.write_str(")) ->", NL_SINGLE, IndentAction.INC)

        return guard


class MessageFlowBuilder(AtomicBuilder):
    pass
