program Core;

procedure bpmnVerify (inout x: int)
spec {
  requires (x == 0);  // from state.txt: var x: int = 0
}
{
  // ── BPMN places — one bool per sequence flow token ──
  var p_start: bool := true;   // initial token (before StartEvent_1 fires)
  var p_flow1: bool := false;  // Flow_1: sourceRef=StartEvent_1  targetRef=Task_1
  var p_flow2: bool := false;  // Flow_2: sourceRef=Task_1        targetRef=Gateway_1
  var p_flow3: bool := false;  // Flow_3: sourceRef=Gateway_1     targetRef=EndEvent_1  conditionExpression: x > 5
  var p_flow4: bool := false;  // Flow_4: sourceRef=Gateway_1     targetRef=Task_1      conditionExpression: x <= 5

  // T_START — startEvent id=StartEvent_1: consume p_start, produce p_flow1
  p_start := false;
  p_flow1 := true;

  while (p_flow1 || p_flow4)
    decreases 6 - x
    invariant 0 <= x
    invariant x <= 6
    invariant (!(p_flow1 || p_flow4) || x <= 5)  // if a token is waiting for Task_1, x must be <= 5
    invariant (!p_flow3 || x > 5)                // if a token has reached EndEvent_1, x must be > 5
    invariant (p_flow1 || p_flow4 || p_flow3)    // a token is always in one of these places
  {
    // T_INCREMENT — task id=Task_1: consume p_flow1 or p_flow4, run <documentation>, produce p_flow2
    x := x + 1;
    p_flow1 := false;
    p_flow4 := false;

    // Transition to Gateway_1
    p_flow2 := true;

    if (x > 5) {
      // T_GW_TO_END — exclusiveGateway id=Gateway_1 via Flow_3 (x > 5)
      assert [gw_to_end]: (x > 5);  // CWP: Increment_x → End requires x > 5
      p_flow2 := false;
      p_flow3 := true;
    } else {
      // T_GW_TO_LOOP — exclusiveGateway id=Gateway_1 via Flow_4 (x <= 5)
      assert [gw_to_loop]: (x <= 5);  // CWP: looping back requires x <= 5
      p_flow2 := false;
      p_flow4 := true;
    }
  }

  // T_END — endEvent id=EndEvent_1: consume p_flow3, workflow complete
  assert [increment_to_end]: (x > 5);  // CWP: End requires x > 5
  p_flow3 := false;
};
