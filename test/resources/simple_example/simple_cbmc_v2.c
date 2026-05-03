#include <stdbool.h>

/* ── CBMC primitive — symbolic (unconstrained) integer ── */
int nondet_int();

/* ── Transition IDs ── */
#define T_START      0   // startEvent      id=StartEvent_1
#define T_INCREMENT  1   // task            id=Task_1
#define T_GW_TO_END  2   // exclusiveGateway id=Gateway_1  via Flow_3 (x > 5)
#define T_GW_TO_LOOP 3   // exclusiveGateway id=Gateway_1  via Flow_4 (x <= 5)
#define T_END        4   // endEvent        id=EndEvent_1

#define BOUND 30

int main() {
    /* ── State variables (from state.txt) ── */
    int x = 0;

    /* ── BPMN places — one bool per sequence flow token ── */
    bool p_start = true;   // initial token (before StartEvent_1 fires)
    bool p_flow1 = false;  // Flow_1: sourceRef=StartEvent_1  targetRef=Task_1
    bool p_flow2 = false;  // Flow_2: sourceRef=Task_1        targetRef=Gateway_1
    bool p_flow3 = false;  // Flow_3: sourceRef=Gateway_1     targetRef=EndEvent_1  conditionExpression: x > 5
    bool p_flow4 = false;  // Flow_4: sourceRef=Gateway_1     targetRef=Task_1      conditionExpression: x <= 5

    for (int step = 0; step < BOUND; step++) {

        /* Non-deterministically pick a transition to fire */
        int choice = nondet_int();

        /* Constrain choice to an *enabled* transition only */
        __CPROVER_assume(
            (choice == T_START      &&  p_start)                 ||
            (choice == T_INCREMENT  && (p_flow1 || p_flow4))     ||
            (choice == T_GW_TO_END  &&  p_flow2 && x > 5)        ||
            (choice == T_GW_TO_LOOP &&  p_flow2 && x <= 5)       ||
            (choice == T_END        &&  p_flow3)
        );

        /* Fire the chosen transition */
        if (choice == T_START) {
            // startEvent id=StartEvent_1: consume initial token, produce Flow_1
            p_start = false;
            p_flow1 = true;

        } else if (choice == T_INCREMENT) {
            // task id=Task_1: consume Flow_1 or Flow_4, run <documentation>, produce Flow_2
            p_flow1 = false;
            p_flow4 = false;
            x = x + 1;  // <documentation> x = x + 1 </documentation>
            p_flow2 = true;

        } else if (choice == T_GW_TO_END) {
            // exclusiveGateway id=Gateway_1: consume Flow_2, produce Flow_3 (x > 5)
            __CPROVER_assert(x > 5, "CWP: taking End path requires x > 5");
            p_flow2 = false;
            p_flow3 = true;

        } else if (choice == T_GW_TO_LOOP) {
            // exclusiveGateway id=Gateway_1: consume Flow_2, produce Flow_4 (x <= 5)
            __CPROVER_assert(x <= 5, "CWP: taking loop path requires x <= 5");
            p_flow2 = false;
            p_flow4 = true;

        } else if (choice == T_END) {
            // endEvent id=EndEvent_1: consume Flow_3, workflow complete
            p_flow3 = false;
            break;
        }
    }

    return 0;
}
