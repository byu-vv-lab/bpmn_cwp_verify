#include <stdbool.h>

/* ── CBMC primitive — symbolic (unconstrained) integer ── */
int nondet_int();

int main() {
    /* ── State variables (from state.txt) ── */
    int x = 0;

    /* ── BPMN places — one bool per sequence flow token ── */
    bool p_start = true;   // initial token (before StartEvent_1 fires)
    bool p_flow1 = false;  // Flow_1: sourceRef=StartEvent_1  targetRef=Task_1
    bool p_flow2 = false;  // Flow_2: sourceRef=Task_1        targetRef=Gateway_1
    bool p_flow3 = false;  // Flow_3: sourceRef=Gateway_1     targetRef=EndEvent_1  conditionExpression: x > 5
    bool p_flow4 = false;  // Flow_4: sourceRef=Gateway_1     targetRef=Task_1      conditionExpression: x <= 5

    // T_START
    p_start = false;
    p_flow1 = true;

    /* Loop while a token is waiting at Task_1 — terminates when the gateway
       routes to EndEvent_1.  Use --unwind N on the command line for the bound. */
    while (p_flow1 || p_flow4) {

        /* T_INCREMENT — task contract: we don't specify exactly what the task
           does, only what it preserves.  The task increments x by 1 or 2
           (non-deterministic).  CBMC explores both choices at every iteration. */
        int delta = nondet_int();
        __CPROVER_assume(delta == 1 || delta == 2);
        x = x + delta;

        p_flow1 = false;
        p_flow4 = false;
        p_flow2 = true;

        if (x > 5) {
            // T_GW_TO_END — exclusiveGateway via Flow_3 (x > 5)
            __CPROVER_assert(x > 5, "CWP: taking End path requires x > 5");
            p_flow2 = false;
            p_flow3 = true;
        } else {
            // T_GW_TO_LOOP — exclusiveGateway via Flow_4 (x <= 5)
            __CPROVER_assert(x <= 5, "CWP: taking loop path requires x <= 5");
            p_flow2 = false;
            p_flow4 = true;
        }
    }

    // T_END — verify terminal CWP condition holds on all paths
    __CPROVER_assert(x > 5, "CWP: End requires x > 5");
    p_flow3 = false;

    return 0;
}
