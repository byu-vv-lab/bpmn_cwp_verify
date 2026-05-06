/*
 * face2face_cbmc_v2.c — Petri-net token encoding of the face2face workflow
 *
 * Structure (mirrors valid_output.pml):
 *   - One bool per BPMN sequence-flow edge (token place)
 *   - One transition ID per node (task, gateway, event)
 *   - Scheduling loop: nondet_int() picks which transition fires;
 *     __CPROVER_assume constrains choice to currently-enabled transitions only
 *
 * Gateway_12r266n ("both") is an OR-merge + AND-split, not a pure AND-join.
 * Its two incoming flows are mutually exclusive in time (initial entry vs.
 * retry loop), so the guard is || not &&.  It produces tokens on both
 * outgoing flows simultaneously (the AND-split).
 *
 * cbmc face2face_cbmc_v2.c --unwind 10
 * cbmc face2face_cbmc_v2.c --unwind 10 --no-unwinding-assertions
 */

#include <stdbool.h>

int nondet_int();

#define PAYMENT_AMOUNT       253
#define BELOW_PAYMENT_AMOUNT 252
#define NO_RETRY_PAYMENT     254
#define PENDING_PAYMENT      255

#define TERMS_AGREED   0
#define TERMS_FAILED   1
#define TERMS_PENDING  2
#define TERMS_NO_RETRY 3

#define BUYER_NAME   0
#define SELLER_NAME  1

#define T_START_EVENT          0
#define T_TASK1_MEET           1   // Activity_1qm7qck
#define T_GW_BOTH              2   // Gateway_12r266n: OR-merge + AND-split
#define T_TASK2_TERMS          3   // Activity_1unsjkg
#define T_TASK3_PRICE          4   // Activity_1t579ox
#define T_GW_BOTH_JOIN         5   // Gateway_0s1i42o: AND-join
#define T_GW_DEC_AGREED        6   // Gateway_1pm4ghz → agreed
#define T_GW_DEC_NORETRY       7   // Gateway_1pm4ghz → noRetry / failed
#define T_GW_DEC_RETRY_PRICE   8   // Gateway_1pm4ghz → retry price
#define T_GW_DEC_RETRY_TERMS   9   // Gateway_1pm4ghz → retry terms
#define T_GW_DEC_RETRY_BOTH   10   // Gateway_1pm4ghz → retry both
#define T_TASK4_RETRY_PRICE   11   // Activity_1bckz5y
#define T_TASK5_RETRY_TERMS   12   // Activity_1mktua2
#define T_TASK6_HANDSHAKE     13   // Activity_0a5xzqf
#define T_GW_EXCH_SPLIT       14   // Gateway_000lymc: AND-split
#define T_TASK7A_PAYMENT      15   // Activity_1qqx4aq
#define T_TASK7B_BACKPACK     16   // Activity_1rfm4sh
#define T_GW_EXCH_JOIN        17   // Gateway_0cy7rs7: AND-join
#define T_END_COMPLETED       18   // Event_1y6wxsp
#define T_END_FAILED          19   // Event_0wqympo

int main() {

    int terms          = TERMS_PENDING;
    int backpackOwner  = SELLER_NAME;
    int paymentOwner   = BUYER_NAME;
    int paymentOffered = PENDING_PAYMENT;

    /* One bool per sequence-flow edge. Naming: p_<target>_FROM_<source> */
    bool p_start                  = true;
    bool p_task1_FROM_start       = false;  // Flow_0oiwgjd

    /* Gateway_12r266n: two incoming flows (OR-merge) */
    bool p_gwboth_FROM_task1      = false;  // Flow_1wl740o  initial entry
    bool p_gwboth_FROM_gwdec      = false;  // Flow_08e7qxg  retry-both loop

    /* AND-split outgoing: both go live simultaneously on T_GW_BOTH */
    bool p_task2_FROM_gwboth      = false;  // Flow_1kx5xjv
    bool p_task3_FROM_gwboth      = false;  // Flow_13xpfx7

    /* AND-join inputs: both must be true before T_GW_BOTH_JOIN can fire */
    bool p_gwjoin_FROM_task2      = false;  // Flow_1oezfcg
    bool p_gwjoin_FROM_task3      = false;  // Flow_14s5onf

    /* Exclusive gateway: three possible inputs, one fires at a time */
    bool p_gwdec_FROM_join        = false;  // Flow_0feadgd
    bool p_gwdec_FROM_task4       = false;  // Flow_127sd29
    bool p_gwdec_FROM_task5       = false;  // Flow_00oxr95

    bool p_task6_FROM_gwdec       = false;  // Flow_0yqye0v  agreed
    bool p_endfail_FROM_gwdec     = false;  // Flow_0diuub0  noRetry
    bool p_task4_FROM_gwdec       = false;  // Flow_0q6dz8p  retry price
    bool p_task5_FROM_gwdec       = false;  // Flow_0koz64j  retry terms
    /* p_gwboth_FROM_gwdec: retry-both path, declared above */

    bool p_gwexch_FROM_task6      = false;  // Flow_0ct87dl

    /* AND-split outgoing: both go live simultaneously on T_GW_EXCH_SPLIT */
    bool p_task7a_FROM_gwexch     = false;  // Flow_0jmvvxc
    bool p_task7b_FROM_gwexch     = false;  // Flow_1y66pph

    /* AND-join inputs: both must be true before T_GW_EXCH_JOIN can fire */
    bool p_gwexchjoin_FROM_task7a = false;  // Flow_0znbe82
    bool p_gwexchjoin_FROM_task7b = false;  // Flow_1sx1rdt

    bool p_endok_FROM_gwexchjoin  = false;  // Flow_1cm84v3

    bool running = true;
    while (running) {

        int choice = nondet_int();

        bool en_start    = p_start;
        bool en_task1    = p_task1_FROM_start;

        /* OR-merge: fires when either incoming token is present */
        bool en_gwboth   = p_gwboth_FROM_task1 || p_gwboth_FROM_gwdec;

        bool en_task2    = p_task2_FROM_gwboth;
        bool en_task3    = p_task3_FROM_gwboth;

        /* AND-join guard IS the wait condition: blocks until both branches complete */
        bool en_gwjoin   = p_gwjoin_FROM_task2 && p_gwjoin_FROM_task3;

        bool en_gwdec    = p_gwdec_FROM_join || p_gwdec_FROM_task4 || p_gwdec_FROM_task5;

        /* Routing conditions can overlap — CBMC non-deterministically picks any
           applicable route, matching SPIN's overlapping if-statement guards */
        bool en_agreed      = en_gwdec && (paymentOffered == PAYMENT_AMOUNT && terms == TERMS_AGREED);
        bool en_noretry     = en_gwdec && (paymentOffered == NO_RETRY_PAYMENT || terms == TERMS_NO_RETRY);
        bool en_retry_price = en_gwdec && (paymentOffered < PAYMENT_AMOUNT);
        bool en_retry_terms = en_gwdec && (terms == TERMS_FAILED);
        bool en_retry_both  = en_gwdec && (paymentOffered < PAYMENT_AMOUNT) && (terms == TERMS_FAILED);

        bool en_task4       = p_task4_FROM_gwdec;
        bool en_task5       = p_task5_FROM_gwdec;
        bool en_task6       = p_task6_FROM_gwdec;
        bool en_gwexch      = p_gwexch_FROM_task6;
        bool en_task7a      = p_task7a_FROM_gwexch;
        bool en_task7b      = p_task7b_FROM_gwexch;

        /* AND-join guard: blocks until both exchange branches complete */
        bool en_gwexchjoin  = p_gwexchjoin_FROM_task7a && p_gwexchjoin_FROM_task7b;

        bool en_endok       = p_endok_FROM_gwexchjoin;
        bool en_endfail     = p_endfail_FROM_gwdec;

        __CPROVER_assume(
            (choice == T_START_EVENT        && en_start)       ||
            (choice == T_TASK1_MEET         && en_task1)       ||
            (choice == T_GW_BOTH            && en_gwboth)      ||
            (choice == T_TASK2_TERMS        && en_task2)       ||
            (choice == T_TASK3_PRICE        && en_task3)       ||
            (choice == T_GW_BOTH_JOIN       && en_gwjoin)      ||
            (choice == T_GW_DEC_AGREED      && en_agreed)      ||
            (choice == T_GW_DEC_NORETRY     && en_noretry)     ||
            (choice == T_GW_DEC_RETRY_PRICE && en_retry_price) ||
            (choice == T_GW_DEC_RETRY_TERMS && en_retry_terms) ||
            (choice == T_GW_DEC_RETRY_BOTH  && en_retry_both)  ||
            (choice == T_TASK4_RETRY_PRICE  && en_task4)       ||
            (choice == T_TASK5_RETRY_TERMS  && en_task5)       ||
            (choice == T_TASK6_HANDSHAKE    && en_task6)       ||
            (choice == T_GW_EXCH_SPLIT      && en_gwexch)      ||
            (choice == T_TASK7A_PAYMENT     && en_task7a)      ||
            (choice == T_TASK7B_BACKPACK    && en_task7b)      ||
            (choice == T_GW_EXCH_JOIN       && en_gwexchjoin)  ||
            (choice == T_END_COMPLETED      && en_endok)       ||
            (choice == T_END_FAILED         && en_endfail)
        );

        if (choice == T_START_EVENT) {
            p_start            = false;
            p_task1_FROM_start = true;

        } else if (choice == T_TASK1_MEET) {
            backpackOwner = SELLER_NAME;
            paymentOwner  = BUYER_NAME;
            __CPROVER_assert(
                paymentOwner == BUYER_NAME && backpackOwner == SELLER_NAME,
                "CWP: Init — buyer holds payment, seller holds backpack");
            p_task1_FROM_start  = false;
            p_gwboth_FROM_task1 = true;

        } else if (choice == T_GW_BOTH) {
            /* OR-merge: clear both (only one is set at a time).
               AND-split: put tokens on both outgoing flows simultaneously. */
            p_gwboth_FROM_task1 = false;
            p_gwboth_FROM_gwdec = false;
            p_task2_FROM_gwboth = true;
            p_task3_FROM_gwboth = true;

        } else if (choice == T_TASK2_TERMS) {
            /* noRetry not possible here — only reachable after T_TASK5_RETRY_TERMS */
            int t = nondet_int();
            __CPROVER_assume(t == TERMS_AGREED || t == TERMS_FAILED);
            terms               = t;
            p_task2_FROM_gwboth = false;
            p_gwjoin_FROM_task2 = true;

        } else if (choice == T_TASK3_PRICE) {
            /* noRetryPayment not possible here — only reachable after T_TASK4_RETRY_PRICE */
            int p = nondet_int();
            __CPROVER_assume(p == PAYMENT_AMOUNT || p == BELOW_PAYMENT_AMOUNT);
            paymentOffered      = p;
            p_task3_FROM_gwboth = false;
            p_gwjoin_FROM_task3 = true;

        } else if (choice == T_GW_BOTH_JOIN) {
            p_gwjoin_FROM_task2 = false;
            p_gwjoin_FROM_task3 = false;
            p_gwdec_FROM_join   = true;

        } else if (choice == T_GW_DEC_AGREED) {
            __CPROVER_assert(
                terms == TERMS_AGREED && paymentOffered == PAYMENT_AMOUNT,
                "CWP: Purchase Agreed — terms and payment both satisfied");
            /* Clear all three inputs (only one is set — matches Promela consumeToken pattern) */
            p_gwdec_FROM_join  = false;
            p_gwdec_FROM_task4 = false;
            p_gwdec_FROM_task5 = false;
            p_task6_FROM_gwdec = true;

        } else if (choice == T_GW_DEC_NORETRY) {
            __CPROVER_assert(
                paymentOffered == NO_RETRY_PAYMENT || terms == TERMS_NO_RETRY,
                "CWP: Purchase Failed — noRetry condition reached");
            p_gwdec_FROM_join    = false;
            p_gwdec_FROM_task4   = false;
            p_gwdec_FROM_task5   = false;
            p_endfail_FROM_gwdec = true;

        } else if (choice == T_GW_DEC_RETRY_PRICE) {
            p_gwdec_FROM_join  = false;
            p_gwdec_FROM_task4 = false;
            p_gwdec_FROM_task5 = false;
            p_task4_FROM_gwdec = true;

        } else if (choice == T_GW_DEC_RETRY_TERMS) {
            p_gwdec_FROM_join  = false;
            p_gwdec_FROM_task4 = false;
            p_gwdec_FROM_task5 = false;
            p_task5_FROM_gwdec = true;

        } else if (choice == T_GW_DEC_RETRY_BOTH) {
            p_gwdec_FROM_join    = false;
            p_gwdec_FROM_task4   = false;
            p_gwdec_FROM_task5   = false;
            p_gwboth_FROM_gwdec  = true;

        } else if (choice == T_TASK4_RETRY_PRICE) {
            /* noRetryPayment now possible */
            int p = nondet_int();
            __CPROVER_assume(p == PAYMENT_AMOUNT || p == BELOW_PAYMENT_AMOUNT || p == NO_RETRY_PAYMENT);
            paymentOffered     = p;
            p_task4_FROM_gwdec = false;
            p_gwdec_FROM_task4 = true;

        } else if (choice == T_TASK5_RETRY_TERMS) {
            /* noRetry now possible */
            int t = nondet_int();
            __CPROVER_assume(t == TERMS_AGREED || t == TERMS_FAILED || t == TERMS_NO_RETRY);
            terms              = t;
            p_task5_FROM_gwdec = false;
            p_gwdec_FROM_task5 = true;

        } else if (choice == T_TASK6_HANDSHAKE) {
            p_task6_FROM_gwdec  = false;
            p_gwexch_FROM_task6 = true;

        } else if (choice == T_GW_EXCH_SPLIT) {
            p_gwexch_FROM_task6  = false;
            p_task7a_FROM_gwexch = true;
            p_task7b_FROM_gwexch = true;

        } else if (choice == T_TASK7A_PAYMENT) {
            paymentOwner             = SELLER_NAME;
            p_task7a_FROM_gwexch     = false;
            p_gwexchjoin_FROM_task7a = true;

        } else if (choice == T_TASK7B_BACKPACK) {
            backpackOwner            = BUYER_NAME;
            p_task7b_FROM_gwexch     = false;
            p_gwexchjoin_FROM_task7b = true;

        } else if (choice == T_GW_EXCH_JOIN) {
            __CPROVER_assert(
                paymentOwner == SELLER_NAME && backpackOwner == BUYER_NAME,
                "CWP: Ownerships Switched — seller has payment, buyer has backpack");
            p_gwexchjoin_FROM_task7a = false;
            p_gwexchjoin_FROM_task7b = false;
            p_endok_FROM_gwexchjoin  = true;

        } else if (choice == T_END_COMPLETED) {
            p_endok_FROM_gwexchjoin = false;
            running = false;

        } else if (choice == T_END_FAILED) {
            __CPROVER_assert(
                paymentOffered == NO_RETRY_PAYMENT || terms == TERMS_NO_RETRY,
                "CWP: Purchase Failed terminal — noRetry condition holds");
            p_endfail_FROM_gwdec = false;
            running = false;
        }
    }

    return 0;
}
