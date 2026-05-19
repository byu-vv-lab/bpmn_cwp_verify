/*
 * face2face_cbmc_v2.c — Two-pool Petri-net token encoding of the face2face workflow
 *
 * Scenario:
 *   Buyer:  wants to buy a backpack; starts with payment (cash).
 *   Seller: wants to sell a backpack; starts owning the backpack.
 *
 * Pool structure:
 *   Two participants modeled as a single C process with interleaved transitions.
 *   Each pool has its own plain start event (see note on message start events below).
 *   The two start tokens are consumed by T_MEET, which acts as an AND-join:
 *   negotiation cannot begin until both the Buyer and Seller have started.
 *
 * Note on message start events (issue #324):
 *   In a canonical two-pool BPMN for this scenario the Seller's process would
 *   use a message start event — the Seller's process activates only when the
 *   Buyer sends the first contact message.  Message start events are NOT
 *   supported in this CBMC encoding: their semantics require inter-process
 *   threading and message correlation that the single-process token model
 *   cannot express.  We model the Seller with a plain start event instead.
 *   Both parties start concurrently; coordination is through shared state.
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
 * Loop bound:
 *   BOUND = acyclic_path (14) + retry_loop_length (5) * MAX_RETRIES (2) + buffer (2) = 26
 *   Acyclic happy path is 14 transitions (vs 13 in the single-pool model — the
 *   two separate start events add one net transition before the meet point).
 *   Each retry-both cycle adds 5 steps:
 *     T_GW_DEC_RETRY_BOTH + T_GW_BOTH + T_TASK2_TERMS + T_TASK3_PRICE + T_GW_BOTH_JOIN
 *   MAX_RETRIES caps how many times any retry branch can fire; retry_count
 *   enforces this in the enable conditions so CBMC never explores deeper paths.
 *   Pass --unwind (BOUND + 1) to cover the loop termination check.
 *
 * cbmc test/resources/face2face/face2face_cbmc_v2.c --unwind 26
 *
 * Reachability checks (end events + all CWP states):
 *   cbmc test/resources/face2face/face2face_cbmc_v2.c --unwind 26 --cover cover -DREACHABILITY
 *   expect: 7 of 7 covered (100%)
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

/* BOUND = acyclic_path(14) + retry_loop_length(5) * MAX_RETRIES(2) + buffer(2) */
#define MAX_RETRIES 2
#define BOUND       26

/* ── CWP state IDs ───────────────────────────────────────────────────────── */
/* Mirror the transition-ID pattern: named integers, one per CWP state.      */
#define CWP_INIT          0   // Init Purchase Pending (initial state)
#define CWP_NEGOTIATIONS  1   // Negotiations
#define CWP_AGREED        2   // Purchase Agreed
#define CWP_FAILED        3   // Purchase Failed (terminal)
#define CWP_SWITCHED      4   // Ownerships Switched (terminal)
#define CWP_NUM_STATES    5

/* ── Transition IDs ───────────────────────────────────────────────────────── */

/* Buyer pool */
#define T_BUYER_START          0   // Buyer plain start event — Buyer wants to buy a backpack

/* Seller pool */
#define T_SELLER_START         1   // Seller plain start event — Seller wants to sell a backpack
                                   // NOTE: in canonical BPMN this would be a message start event
                                   // (triggered by first Buyer contact).  Message start events are
                                   // unsupported here — see issue #324 and file header.

/* Shared workflow — both pools participate from here on */
#define T_MEET                 2   // AND-join: Buyer and Seller meet (both start tokens consumed)
#define T_GW_BOTH              3   // Gateway_12r266n: OR-merge + AND-split
#define T_TASK2_TERMS          4   // Activity_1unsjkg: Seller states terms; Buyer evaluates
#define T_TASK3_PRICE          5   // Activity_1t579ox: Buyer offers price; Seller evaluates
#define T_GW_BOTH_JOIN         6   // Gateway_0s1i42o: AND-join
#define T_GW_DEC_AGREED        7   // Gateway_1pm4ghz → agreed
#define T_GW_DEC_NORETRY       8   // Gateway_1pm4ghz → noRetry / failed
#define T_GW_DEC_RETRY_PRICE   9   // Gateway_1pm4ghz → retry price
#define T_GW_DEC_RETRY_TERMS  10   // Gateway_1pm4ghz → retry terms
#define T_GW_DEC_RETRY_BOTH   11   // Gateway_1pm4ghz → retry both
#define T_TASK4_RETRY_PRICE   12   // Activity_1bckz5y: Buyer revises price offer
#define T_TASK5_RETRY_TERMS   13   // Activity_1mktua2: Seller revises terms
#define T_TASK6_HANDSHAKE     14   // Activity_0a5xzqf: Buyer and Seller shake hands
#define T_GW_EXCH_SPLIT       15   // Gateway_000lymc: AND-split (simultaneous exchange)
#define T_TASK7A_PAYMENT      16   // Activity_1qqx4aq: Buyer hands payment to Seller
#define T_TASK7B_BACKPACK     17   // Activity_1rfm4sh: Seller hands backpack to Buyer
#define T_GW_EXCH_JOIN        18   // Gateway_0cy7rs7: AND-join (exchange complete)
#define T_END_COMPLETED       19   // Event_1y6wxsp:   Purchase Completed
#define T_END_FAILED          20   // Event_0wqympo:   Purchase Failed

/*
 * update_cwp_state — recompute CWP state after any shared-variable change.
 *
 * Call after every task that modifies terms, paymentOffered, paymentOwner,
 * or backpackOwner.  Asserts three structural CWP properties:
 *
 *   P1: the (old → new) state transition follows a valid CWP edge
 *   P2: exactly one CWP state is active after the update (mutual exclusion)
 *   P3: at least one CWP state is active after the update (always-in-a-state)
 *
 * State invariants use the CWP rule:
 *   in_state_S ≡ (all incoming-edge conditions hold) ∧ ¬(any outgoing-edge condition holds)
 *
 * CWP edges (from cwp.xml):
 *   Init  → Negotiations : terms != PENDING  || paymentOffered != PENDING_PAYMENT
 *   Neg   → Agreed       : terms == AGREED   && paymentOffered == PAYMENT_AMOUNT
 *   Neg   → Failed       : terms == NO_RETRY || paymentOffered == NO_RETRY_PAYMENT
 *   Agreed→ Switched     : paymentOwner == SELLER && backpackOwner == BUYER
 */
static void update_cwp_state(bool cwp[], int paymentOwner, int backpackOwner,
                              int terms, int paymentOffered)
{
    /* Snapshot old state before overwriting */
    bool old[CWP_NUM_STATES];
    for (int i = 0; i < CWP_NUM_STATES; i++) old[i] = cwp[i];

    /* CWP edge conditions */
    bool e_init_to_neg      = (terms != TERMS_PENDING || paymentOffered != PENDING_PAYMENT);
    bool e_neg_to_agreed    = (terms == TERMS_AGREED && paymentOffered == PAYMENT_AMOUNT);
    bool e_neg_to_failed    = (terms == TERMS_NO_RETRY || paymentOffered == NO_RETRY_PAYMENT);
    bool e_agreed_to_switch = (paymentOwner == SELLER_NAME && backpackOwner == BUYER_NAME);

    /* Next state: conjunction of incoming-edge conditions, negation of outgoing */
    bool next[CWP_NUM_STATES];
    next[CWP_INIT]         = !e_init_to_neg;
    next[CWP_NEGOTIATIONS] =  e_init_to_neg && !e_neg_to_agreed && !e_neg_to_failed;
    next[CWP_AGREED]       =  e_neg_to_agreed && !e_agreed_to_switch;
    next[CWP_FAILED]       =  e_neg_to_failed;
    next[CWP_SWITCHED]     =  e_agreed_to_switch;

    /* P1: transition follows a valid CWP edge (or stays in same state) */
    __CPROVER_assert(
        (old[CWP_INIT]         && next[CWP_INIT])         ||  /* stay           */
        (old[CWP_NEGOTIATIONS] && next[CWP_NEGOTIATIONS]) ||  /* stay           */
        (old[CWP_AGREED]       && next[CWP_AGREED])       ||  /* stay           */
        (old[CWP_FAILED]       && next[CWP_FAILED])       ||  /* stay           */
        (old[CWP_SWITCHED]     && next[CWP_SWITCHED])     ||  /* stay           */
        (old[CWP_INIT]         && next[CWP_NEGOTIATIONS]) ||  /* init → neg     */
        (old[CWP_NEGOTIATIONS] && next[CWP_AGREED])       ||  /* neg  → agreed  */
        (old[CWP_NEGOTIATIONS] && next[CWP_FAILED])       ||  /* neg  → failed  */
        (old[CWP_AGREED]       && next[CWP_SWITCHED]),        /* agreed → sw    */
        "CWP P1: transition follows valid CWP edge");

    /* P2: exactly one CWP state active (mutual exclusion) */
    int active = 0;
    for (int i = 0; i < CWP_NUM_STATES; i++) active += next[i] ? 1 : 0;
    __CPROVER_assert(active == 1, "CWP P2: exactly one CWP state active");

    /* P3: always in some CWP state (implied by P2, but explicit for traceability) */
    __CPROVER_assert(
        next[CWP_INIT] || next[CWP_NEGOTIATIONS] || next[CWP_AGREED] ||
        next[CWP_FAILED] || next[CWP_SWITCHED],
        "CWP P3: always in some CWP state");

    /* Commit next state */
    for (int i = 0; i < CWP_NUM_STATES; i++) cwp[i] = next[i];
}

int main() {

    int terms          = TERMS_PENDING;
    int backpackOwner  = SELLER_NAME;   // Seller starts with the backpack
    int paymentOwner   = BUYER_NAME;    // Buyer starts with the payment
    int paymentOffered = PENDING_PAYMENT;

    /* ── Token places — one bool per sequence-flow edge ──────────────────── */

    /* Buyer pool: plain start event */
    bool p_buyer_start         = true;
    bool p_buyer_FROM_start    = false;

    /* Seller pool: plain start event (NOT message start — see issue #324) */
    bool p_seller_start        = true;
    bool p_seller_FROM_start   = false;

    /* Meet point: AND-join consuming both start tokens */
    /* Gateway_12r266n: two incoming flows (OR-merge) */
    bool p_gwboth_FROM_meet    = false;  // Flow_1wl740o  initial entry (after T_MEET)
    bool p_gwboth_FROM_gwdec   = false;  // Flow_08e7qxg  retry-both loop

    /* AND-split outgoing: both go live simultaneously on T_GW_BOTH */
    bool p_task2_FROM_gwboth   = false;  // Flow_1kx5xjv
    bool p_task3_FROM_gwboth   = false;  // Flow_13xpfx7

    /* AND-join inputs: both must be true before T_GW_BOTH_JOIN can fire */
    bool p_gwjoin_FROM_task2   = false;  // Flow_1oezfcg
    bool p_gwjoin_FROM_task3   = false;  // Flow_14s5onf

    /* Exclusive gateway: three possible inputs, one fires at a time */
    bool p_gwdec_FROM_join     = false;  // Flow_0feadgd
    bool p_gwdec_FROM_task4    = false;  // Flow_127sd29
    bool p_gwdec_FROM_task5    = false;  // Flow_00oxr95

    bool p_task6_FROM_gwdec    = false;  // Flow_0yqye0v  agreed
    bool p_endfail_FROM_gwdec  = false;  // Flow_0diuub0  noRetry
    bool p_task4_FROM_gwdec    = false;  // Flow_0q6dz8p  retry price
    bool p_task5_FROM_gwdec    = false;  // Flow_0koz64j  retry terms
    /* p_gwboth_FROM_gwdec: retry-both path, declared above */

    bool p_gwexch_FROM_task6   = false;  // Flow_0ct87dl

    /* AND-split outgoing: both go live simultaneously on T_GW_EXCH_SPLIT */
    bool p_task7a_FROM_gwexch  = false;  // Flow_0jmvvxc
    bool p_task7b_FROM_gwexch  = false;  // Flow_1y66pph

    /* AND-join inputs: both must be true before T_GW_EXCH_JOIN can fire */
    bool p_gwexchjoin_FROM_task7a = false;  // Flow_0znbe82
    bool p_gwexchjoin_FROM_task7b = false;  // Flow_1sx1rdt

    bool p_endok_FROM_gwexchjoin  = false;  // Flow_1cm84v3

    /* Reachability tracking */
    bool end_completed_reached = false;
    bool end_failed_reached    = false;

    /* ── CWP state tracking ──────────────────────────────────────────────── */
    /* cwp[S] == true means the workflow is currently in CWP state S.        */
    /* Initial variable values satisfy Init Purchase Pending, so start there. */
    bool cwp[CWP_NUM_STATES] = {true, false, false, false, false};

    /* CWP state reachability tracking — mirrors end_completed_reached pattern.
     * cwp_reached[S] becomes true the first time the workflow enters state S. */
    bool cwp_reached[CWP_NUM_STATES] = {true, false, false, false, false};

    bool running = true;
    int step = 0;
    int retry_count = 0;
    while (running && step < BOUND) {

        int choice = nondet_int();

        /* ── Enable conditions ────────────────────────────────────────────── */

        bool en_buyer_start  = p_buyer_start;
        bool en_seller_start = p_seller_start;

        /* AND-join: both Buyer and Seller must have started before they can meet */
        bool en_meet    = p_buyer_FROM_start && p_seller_FROM_start;

        /* OR-merge: fires when either incoming token is present */
        bool en_gwboth  = p_gwboth_FROM_meet || p_gwboth_FROM_gwdec;

        bool en_task2   = p_task2_FROM_gwboth;
        bool en_task3   = p_task3_FROM_gwboth;

        /* AND-join guard: blocks until both negotiation branches complete */
        bool en_gwjoin  = p_gwjoin_FROM_task2 && p_gwjoin_FROM_task3;

        bool en_gwdec   = p_gwdec_FROM_join || p_gwdec_FROM_task4 || p_gwdec_FROM_task5;

        /* Routing conditions can overlap — CBMC non-deterministically picks any
           applicable route, matching SPIN's overlapping if-statement guards */
        bool en_agreed      = en_gwdec
                            && (paymentOffered == PAYMENT_AMOUNT)
                            && (terms == TERMS_AGREED)
                            && (retry_count == 0);
        bool en_noretry     = en_gwdec
                            && (paymentOffered == NO_RETRY_PAYMENT || terms == TERMS_NO_RETRY);
        bool en_retry_price = en_gwdec
                            && (paymentOffered < PAYMENT_AMOUNT)
                            && (retry_count < MAX_RETRIES);
        bool en_retry_terms = en_gwdec
                            && (terms == TERMS_FAILED)
                            && (retry_count < MAX_RETRIES);
        bool en_retry_both  = en_gwdec
                            && (paymentOffered < PAYMENT_AMOUNT)
                            && (terms == TERMS_FAILED)
                            && (retry_count < MAX_RETRIES);

        bool en_task4      = p_task4_FROM_gwdec;
        bool en_task5      = p_task5_FROM_gwdec;
        bool en_task6      = p_task6_FROM_gwdec;
        bool en_gwexch     = p_gwexch_FROM_task6;
        bool en_task7a     = p_task7a_FROM_gwexch;
        bool en_task7b     = p_task7b_FROM_gwexch;

        /* AND-join guard: blocks until both exchange branches complete */
        bool en_gwexchjoin = p_gwexchjoin_FROM_task7a && p_gwexchjoin_FROM_task7b;

        bool en_endok      = p_endok_FROM_gwexchjoin;
        bool en_endfail    = p_endfail_FROM_gwdec;

        __CPROVER_assume(
            (choice == T_BUYER_START        && en_buyer_start)  ||
            (choice == T_SELLER_START       && en_seller_start) ||
            (choice == T_MEET               && en_meet)         ||
            (choice == T_GW_BOTH            && en_gwboth)       ||
            (choice == T_TASK2_TERMS        && en_task2)        ||
            (choice == T_TASK3_PRICE        && en_task3)        ||
            (choice == T_GW_BOTH_JOIN       && en_gwjoin)       ||
            (choice == T_GW_DEC_AGREED      && en_agreed)       ||
            (choice == T_GW_DEC_NORETRY     && en_noretry)      ||
            (choice == T_GW_DEC_RETRY_PRICE && en_retry_price)  ||
            (choice == T_GW_DEC_RETRY_TERMS && en_retry_terms)  ||
            (choice == T_GW_DEC_RETRY_BOTH  && en_retry_both)   ||
            (choice == T_TASK4_RETRY_PRICE  && en_task4)        ||
            (choice == T_TASK5_RETRY_TERMS  && en_task5)        ||
            (choice == T_TASK6_HANDSHAKE    && en_task6)        ||
            (choice == T_GW_EXCH_SPLIT      && en_gwexch)       ||
            (choice == T_TASK7A_PAYMENT     && en_task7a)       ||
            (choice == T_TASK7B_BACKPACK    && en_task7b)       ||
            (choice == T_GW_EXCH_JOIN       && en_gwexchjoin)   ||
            (choice == T_END_COMPLETED      && en_endok)        ||
            (choice == T_END_FAILED         && en_endfail)
        );

        /* ── Transition bodies ────────────────────────────────────────────── */

        if (choice == T_BUYER_START) {
            /* Buyer decides to buy a backpack and begins looking for a seller */
            p_buyer_start       = false;
            p_buyer_FROM_start  = true;

        } else if (choice == T_SELLER_START) {
            /* Seller decides to sell a backpack and makes it available.
             * Plain start event: Seller is independently ready, not waiting for
             * a message.  In canonical BPMN this would be a message start event
             * (activated by Buyer's first contact) — unsupported here (issue #324). */
            p_seller_start      = false;
            p_seller_FROM_start = true;

        } else if (choice == T_MEET) {
            /* AND-join: Buyer finds Seller; negotiation can now begin.
             * Confirms initial ownership: Seller holds the backpack, Buyer holds payment. */
            __CPROVER_assert(
                paymentOwner == BUYER_NAME && backpackOwner == SELLER_NAME,
                "CWP: Init — Buyer holds payment, Seller holds backpack");
            p_buyer_FROM_start  = false;
            p_seller_FROM_start = false;
            p_gwboth_FROM_meet  = true;

        } else if (choice == T_GW_BOTH) {
            /* OR-merge: clear both (only one is set at a time).
               AND-split: put tokens on both outgoing flows simultaneously — parallel
               negotiation of terms and price begins. */
            p_gwboth_FROM_meet  = false;
            p_gwboth_FROM_gwdec = false;
            p_task2_FROM_gwboth = true;
            p_task3_FROM_gwboth = true;

        } else if (choice == T_TASK2_TERMS) {
            /* Seller states terms; Buyer evaluates.
             * noRetry not possible here — only reachable after T_TASK5_RETRY_TERMS */
            int t = nondet_int();
            __CPROVER_assume(t == TERMS_AGREED || t == TERMS_FAILED);
            terms               = t;
            p_task2_FROM_gwboth = false;
            p_gwjoin_FROM_task2 = true;
            update_cwp_state(cwp, paymentOwner, backpackOwner, terms, paymentOffered);
            for (int i = 0; i < CWP_NUM_STATES; i++) cwp_reached[i] |= cwp[i];

        } else if (choice == T_TASK3_PRICE) {
            /* Buyer offers price; Seller evaluates.
             * noRetryPayment not possible here — only reachable after T_TASK4_RETRY_PRICE */
            int p = nondet_int();
            __CPROVER_assume(p == PAYMENT_AMOUNT || p == BELOW_PAYMENT_AMOUNT);
            paymentOffered      = p;
            p_task3_FROM_gwboth = false;
            p_gwjoin_FROM_task3 = true;
            update_cwp_state(cwp, paymentOwner, backpackOwner, terms, paymentOffered);
            for (int i = 0; i < CWP_NUM_STATES; i++) cwp_reached[i] |= cwp[i];

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
            retry_count++;
            p_gwdec_FROM_join  = false;
            p_gwdec_FROM_task4 = false;
            p_gwdec_FROM_task5 = false;
            p_task4_FROM_gwdec = true;

        } else if (choice == T_GW_DEC_RETRY_TERMS) {
            retry_count++;
            p_gwdec_FROM_join  = false;
            p_gwdec_FROM_task4 = false;
            p_gwdec_FROM_task5 = false;
            p_task5_FROM_gwdec = true;

        } else if (choice == T_GW_DEC_RETRY_BOTH) {
            retry_count++;
            p_gwdec_FROM_join   = false;
            p_gwdec_FROM_task4  = false;
            p_gwdec_FROM_task5  = false;
            p_gwboth_FROM_gwdec = true;

        } else if (choice == T_TASK4_RETRY_PRICE) {
            /* Buyer revises price offer; noRetryPayment now possible */
            int p = nondet_int();
            __CPROVER_assume(p == PAYMENT_AMOUNT || p == BELOW_PAYMENT_AMOUNT || p == NO_RETRY_PAYMENT);
            paymentOffered     = p;
            p_task4_FROM_gwdec = false;
            p_gwdec_FROM_task4 = true;
            update_cwp_state(cwp, paymentOwner, backpackOwner, terms, paymentOffered);
            for (int i = 0; i < CWP_NUM_STATES; i++) cwp_reached[i] |= cwp[i];

        } else if (choice == T_TASK5_RETRY_TERMS) {
            /* Seller revises terms; noRetry now possible */
            int t = nondet_int();
            __CPROVER_assume(t == TERMS_AGREED || t == TERMS_FAILED || t == TERMS_NO_RETRY);
            terms              = t;
            p_task5_FROM_gwdec = false;
            p_gwdec_FROM_task5 = true;
            update_cwp_state(cwp, paymentOwner, backpackOwner, terms, paymentOffered);
            for (int i = 0; i < CWP_NUM_STATES; i++) cwp_reached[i] |= cwp[i];

        } else if (choice == T_TASK6_HANDSHAKE) {
            /* Buyer and Seller shake hands — deal is agreed, exchange begins */
            p_task6_FROM_gwdec  = false;
            p_gwexch_FROM_task6 = true;

        } else if (choice == T_GW_EXCH_SPLIT) {
            /* AND-split: simultaneous exchange begins */
            p_gwexch_FROM_task6  = false;
            p_task7a_FROM_gwexch = true;
            p_task7b_FROM_gwexch = true;

        } else if (choice == T_TASK7A_PAYMENT) {
            /* Buyer hands payment to Seller */
            paymentOwner             = SELLER_NAME;
            p_task7a_FROM_gwexch     = false;
            p_gwexchjoin_FROM_task7a = true;
            update_cwp_state(cwp, paymentOwner, backpackOwner, terms, paymentOffered);
            for (int i = 0; i < CWP_NUM_STATES; i++) cwp_reached[i] |= cwp[i];

        } else if (choice == T_TASK7B_BACKPACK) {
            /* Seller hands backpack to Buyer */
            backpackOwner            = BUYER_NAME;
            p_task7b_FROM_gwexch     = false;
            p_gwexchjoin_FROM_task7b = true;
            update_cwp_state(cwp, paymentOwner, backpackOwner, terms, paymentOffered);
            for (int i = 0; i < CWP_NUM_STATES; i++) cwp_reached[i] |= cwp[i];

        } else if (choice == T_GW_EXCH_JOIN) {
            __CPROVER_assert(
                paymentOwner == SELLER_NAME && backpackOwner == BUYER_NAME,
                "CWP: Ownerships Switched — Seller has payment, Buyer has backpack");
            p_gwexchjoin_FROM_task7a = false;
            p_gwexchjoin_FROM_task7b = false;
            p_endok_FROM_gwexchjoin  = true;

        } else if (choice == T_END_COMPLETED) {
            p_endok_FROM_gwexchjoin = false;
            end_completed_reached   = true;
            running = false;

        } else if (choice == T_END_FAILED) {
            __CPROVER_assert(
                paymentOffered == NO_RETRY_PAYMENT || terms == TERMS_NO_RETRY,
                "CWP: Purchase Failed terminal — noRetry condition holds");
            p_endfail_FROM_gwdec = false;
            end_failed_reached   = true;
            running = false;
        }

        step++;
    }

    /* Reachability checks (4th CWP property).
     *
     * __CPROVER_cover(condition) asks CBMC to find a path making the condition true.
     * Guarded by -DREACHABILITY so the correctness run is not affected.
     *
     * Correctness (all CWP properties hold on all paths):
     *   cbmc test/resources/face2face/face2face_cbmc_v2.c --unwind 26
     *   expect: VERIFICATION SUCCESSFUL
     *
     * Reachability (both end events and every CWP state are reachable):
     *   cbmc test/resources/face2face/face2face_cbmc_v2.c --unwind 26 --cover cover -DREACHABILITY
     *   expect: 7 of 7 covered (100%)
     */
    #ifdef REACHABILITY
        /* End-event reachability */
        __CPROVER_cover(end_completed_reached);
        __CPROVER_cover(end_failed_reached);
        /* CWP state reachability — every state must be visitable on some execution path */
        __CPROVER_cover(cwp_reached[CWP_INIT]);
        __CPROVER_cover(cwp_reached[CWP_NEGOTIATIONS]);
        __CPROVER_cover(cwp_reached[CWP_AGREED]);
        __CPROVER_cover(cwp_reached[CWP_FAILED]);
        __CPROVER_cover(cwp_reached[CWP_SWITCHED]);
    #endif

    return 0;
}
