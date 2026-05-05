#include <stdbool.h>

int main() {
    /* ── State variables (from state.txt) ── */
    int x = 0;

    /* ── BPMN places — one bool per sequence flow token ── */
    bool p_start = true;   // initial token (before StartEvent_1 fires)
    bool p_flow1 = false;  // Flow_1: sourceRef=StartEvent_1  targetRef=Task_1
    bool p_flow2 = false;  // Flow_2: sourceRef=Task_1        targetRef=Gateway_1
    bool p_flow3 = false;  // Flow_3: sourceRef=Gateway_1     targetRef=EndEvent_1  conditionExpression: x > 5
    bool p_flow4 = false;  // Flow_4: sourceRef=Gateway_1     targetRef=Task_1      conditionExpression: x <= 5

    while (x <= 5) {
        __CPROVER_assert(x <= 5, "CWP: taking loop path requires x <= 5");

        p_flow1 = false;
        p_flow4 = false;
        x = x + 1;  // <documentation> x = x + 1 </documentation>
        p_flow2 = true;

        if (x > 5) {
            __CPROVER_assert(x > 5, "CWP: taking End path requires x > 5");
            p_flow2 = false;
            p_flow3 = true;
        } else{
            __CPROVER_assert(x <= 5, "CWP: taking loop path requires x <= 5");
            p_flow2 = false;
            p_flow4 = true;
        }
    }

    __CPROVER_assert(x > 5, "CWP: taking End path requires x > 5");

    return 0;
}
