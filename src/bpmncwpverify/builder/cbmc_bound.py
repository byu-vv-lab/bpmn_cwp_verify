"""
cbmc_bound.py — CBMC loop-bound computation from a BPMN graph.

Computes the minimum unwind depth needed for CBMC to cover all execution paths:

    BOUND = SUM over pools of
              acyclic_path_length + sum(loop_length × trips  for each loop)

where `trips` is the loop's derived trip count when it is a recognisable counter
(see cbmc_trip_count.py) and `max_retries` otherwise.

Entry point: _compute_bound(bpmn, max_retries)
"""

from collections import deque

from bpmncwpverify.builder.cbmc_trip_count import loop_trip_count
from bpmncwpverify.core.bpmn import Bpmn, EndEvent, Node, ParallelGatewayNode
from bpmncwpverify.core.feel import Feel
from bpmncwpverify.core.state import State


def _find_matching_join(fork: ParallelGatewayNode, path: frozenset[str]) -> Node | None:
    """
    Return the immediate post-dominator of an AND-fork: the first node reachable
    from every outgoing branch (i.e., the matching AND-join).
    Returns None if no such node exists in the acyclic subgraph.
    """
    branches = [f.target_node for f in fork.out_flows]
    if len(branches) < 2:
        return None

    def _reachable(start: Node) -> set[str]:
        seen: set[str] = set()
        stack: list[Node] = [start]
        while stack:
            n = stack.pop()
            if n.id in seen or n.id in path:
                continue
            seen.add(n.id)
            for f in n.out_flows:
                stack.append(f.target_node)
        return seen

    common: set[str] = _reachable(branches[0])
    for b in branches[1:]:
        common &= _reachable(b)
    if not common:
        return None

    # BFS from all branches simultaneously to find the closest common node.
    visited: set[str] = {b.id for b in branches}
    queue: deque[Node] = deque(branches)
    while queue:
        node = queue.popleft()
        if node.id in common:
            return node
        for f in node.out_flows:
            t = f.target_node
            if t.id not in visited and t.id not in path:
                visited.add(t.id)
                queue.append(t)
    return None


def _acyclic_depth(node: Node, path: frozenset[str]) -> int:
    """
    Longest path (transition firings) from node to any end event in the acyclic skeleton.
    Back-edges (target already in path) are treated as dead ends (-1).

    AND-fork: both branches fire in separate loop iterations, so sum the branch depths.
        However each branch depth includes the shared suffix after the matching AND-join,
        which must be counted only once. Correction: subtract (n-1) copies of the join depth.
    XOR-split: CBMC explores all branches, so use max to cover the longest one.
    Sequential / join: 1 + max valid continuation.
    Returns -1 if no end event is reachable without a back-edge.
    """
    if node.id in path:
        return -1
    new_path = path | {node.id}
    if isinstance(node, EndEvent):
        return 1
    if not node.out_flows:
        return -1
    child_depths = [_acyclic_depth(f.target_node, new_path) for f in node.out_flows]
    valid = [d for d in child_depths if d >= 0]
    if not valid:
        return -1
    if isinstance(node, ParallelGatewayNode) and node.is_fork:
        if len(valid) > 1:
            join = _find_matching_join(node, new_path)
            if join is not None:
                join_depth = _acyclic_depth(join, new_path)
                if join_depth >= 0:
                    return 1 + sum(valid) - (len(valid) - 1) * join_depth
        return 1 + sum(valid)
    return 1 + max(valid)


def _find_back_edges(
    node: Node,
    gray: set[str],
    black: set[str],
    back_edges: list[tuple[str, str]],
) -> None:
    """DFS coloring to collect back-edges as (source_id, target_id) pairs."""
    if node.id in black or node.id in gray:
        return
    gray.add(node.id)
    for flow in node.out_flows:
        t = flow.target_node
        if t.id in gray:
            back_edges.append((node.id, t.id))
        elif t.id not in black:
            _find_back_edges(t, gray, black, back_edges)
    gray.discard(node.id)
    black.add(node.id)


def _cycle_length_bfs(target: Node, source_id: str) -> int:
    """
    BFS from target to source_id in the forward graph.
    Returns the number of transitions in the cycle (each node = 1 step).
    """
    queue: deque[tuple[Node, int]] = deque([(target, 1)])
    visited: set[str] = {target.id}
    while queue:
        node, dist = queue.popleft()
        if node.id == source_id:
            return dist
        for flow in node.out_flows:
            t = flow.target_node
            if t.id not in visited:
                visited.add(t.id)
                queue.append((t, dist + 1))
    return 2  # fallback: minimum cycle


def _back_edge_guard(
    node_map: dict[str, Node], source_id: str, target_id: str
) -> Feel | None:
    """Condition expression on the sequence flow that closes the loop, if any."""
    source = node_map.get(source_id)
    if source is None:
        return None
    for flow in source.out_flows:
        if flow.target_node.id == target_id:
            return getattr(flow, "expression", None)
    return None


def _loop_body(node_map: dict[str, Node], source_id: str, target_id: str) -> list[Node]:
    """Nodes on some path from the loop entry back round to the back-edge source."""

    def _walk(seed: str, forwards: bool) -> set[str]:
        seen: set[str] = set()
        stack = [seed]
        while stack:
            node_id = stack.pop()
            if node_id in seen or node_id not in node_map:
                continue
            seen.add(node_id)
            node = node_map[node_id]
            if forwards:
                stack.extend(f.target_node.id for f in node.out_flows)
            else:
                stack.extend(f.source_node.id for f in node.in_flows)
        return seen

    reachable_from_entry = _walk(target_id, forwards=True)
    reaches_back_edge = _walk(source_id, forwards=False)
    return [node_map[i] for i in reachable_from_entry & reaches_back_edge]


def _flow_bound(
    start: Node, node_map: dict[str, Node], max_retries: int, state: State | None
) -> int:
    """
    Steps one token needs: acyclic longest path + extra trips per loop.

    Detect back-edges from this start event and group them by loop-entry node. A
    counter loop (`x <= 5` guarding a body that does `x + 1`) gets the trip count
    its data actually implies; every other loop falls back to max_retries.
    """
    acyclic = max(_acyclic_depth(start, frozenset()), 0)

    back_edges: list[tuple[str, str]] = []
    _find_back_edges(start, set(), set(), back_edges)

    # Per loop-entry (back-edge target): keep the largest contribution.
    per_entry: dict[str, int] = {}
    for source_id, target_id in back_edges:
        if target_id not in node_map:
            continue
        cycle_len = _cycle_length_bfs(node_map[target_id], source_id)
        derived = loop_trip_count(
            _back_edge_guard(node_map, source_id, target_id),
            _loop_body(node_map, source_id, target_id),
            state,
        )
        retries = max_retries if derived is None else derived
        per_entry[target_id] = max(per_entry.get(target_id, 0), cycle_len * retries)

    return acyclic + sum(per_entry.values())


def compute_bound(bpmn: Bpmn, max_retries: int, state: State | None = None) -> int:
    """
    Acyclic-skeleton longest path + loop contributions, summed across all pools.

    The generated C interleaves every pool on ONE shared step counter — each pass of
    the loop fires a single transition somewhere in the model — so a step spent in one
    pool is a step unavailable to another. The budget that lets every pool finish is
    therefore the sum of their costs, not the largest of them. Same for a pool with
    several start events: each seeds its own token, and all of them have to run.

    `state` supplies initial variable values so counter loops can have their real
    trip count derived; without it every loop falls back to max_retries.
    """
    return max(
        sum(
            _flow_bound(start, dict(process.all_items()), max_retries, state)
            for process in bpmn.processes.values()
            for start in process.get_start_states().values()
        ),
        1,
    )
