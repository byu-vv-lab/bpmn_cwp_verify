#include <stdbool.h>

/* ── CBMC primitive — symbolic (unconstrained) integer ── */
int nondet_int();

/* ── TermsType (from state.txt) ── */
#define TERMS_AGREED   0
#define TERMS_FAILED   1
#define TERMS_PENDING  2
#define TERMS_NO_RETRY 3

/* ── OwnerType (from state.txt) ── */
#define BUYER_NAME  0
#define SELLER_NAME 1

/* ── paymentOffered values (from state.txt) ── */
#define PAYMENT_AMOUNT       253
#define BELOW_PAYMENT_AMOUNT 252  // paymentOffered < paymentAmount
#define NO_RETRY_PAYMENT     254
#define PENDING_PAYMENT      255

int main() {
   /* ── State variables (from state.txt) ── */
   int terms          = TERMS_PENDING;
   int backpackOwner  = SELLER_NAME;
   int paymentOwner   = BUYER_NAME;
   int paymentOffered = PENDING_PAYMENT;

   /* ── BPMN places — one bool per key flow token ── */
   bool p_start       = true;
   bool p_meet        = false;  // StartEvent → Task 1
   bool p_negotiate   = false;  // at parallel split "both" (Gateway_12r266n) — ready for Tasks 2+3
   bool p_terms_ready = false;  // Task 2 complete
   bool p_price_ready = false;  // Task 3 complete
   bool p_at_gateway  = false;  // at exclusive gateway (Gateway_1pm4ghz)
   bool p_handshake   = false;  // exclusive gateway → Task 6 (agreed path)
   bool p_exchange    = false;  // Task 6 → parallel split "both1" (Gateway_000lymc) — ready for Tasks 7a+7b
   bool p_cash_done   = false;  // Task 7a complete
   bool p_pack_done   = false;  // Task 7b complete
   bool p_success     = false;  // Purchase Completed end event
   bool p_failed      = false;  // Purchase Failed end event

   /* ── StartEvent → Task 1 ── */
   p_start = false;
   p_meet  = true;

   /* Task 1: Buyer sees desired backpack and meets Seller
      Contract: sets initial ownership (deterministic per BPMN documentation) */
   p_meet        = false;
   backpackOwner = SELLER_NAME;
   paymentOwner  = BUYER_NAME;
   p_negotiate   = true;

   /* CWP assertion: Init Purchase Pending
      paymentOwner == buyerName && backpackOwner == sellerName */
   __CPROVER_assert(paymentOwner == BUYER_NAME && backpackOwner == SELLER_NAME,
                  "CWP: Init — buyer holds payment, seller holds backpack");

   /* ── Negotiation loop ──
      Runs while any token is active in the negotiation phase.
      The parallel gateways split/join Tasks 2+3 concurrently; the exclusive
      gateway decides the outcome of each round.
      Use --unwind N on the CBMC command line for the verification bound. */
   while (p_negotiate || p_terms_ready || p_price_ready || p_at_gateway) {

      /* Parallel split "both" (Gateway_12r266n):
         Task 1 / both gateway => Tasks 2 and 3 concurrently */
      if (p_negotiate) {
         p_negotiate = false;

         /* Task 2: Buyer and Seller negotiate terms
            Contract: terms becomes agreed or failed (non-det — no noRetry yet) */
         int t = nondet_int();
         __CPROVER_assume(t == TERMS_AGREED || t == TERMS_FAILED);
         terms          = t;
         p_terms_ready  = true;

         /* Task 3: Buyer and Seller negotiate price
            Contract: paymentOffered becomes paymentAmount or belowPaymentAmount (non-det) */
         int p = nondet_int();
         __CPROVER_assume(p == PAYMENT_AMOUNT || p == BELOW_PAYMENT_AMOUNT);
         paymentOffered = p;
         p_price_ready  = true;
      }

      /* Parallel join "end both" (Gateway_0s1i42o):
         Both Task 2 and Task 3 are done — end both exclusive gateway. */
      if (p_terms_ready && p_price_ready) {
         p_terms_ready = false;
         p_price_ready = false;
         p_at_gateway  = true;
      }

      /* End Both Exclusive gateway (Gateway_1pm4ghz): decides negotiation outcome.
         Five outgoing paths, checked in priority order. */
      if (p_at_gateway) {
         p_at_gateway = false;

         if (paymentOffered < PAYMENT_AMOUNT && terms == TERMS_FAILED) {
            /* Flow_08e7qxg: both failed → restart full negotiation (Tasks 2+3) */
            p_negotiate = true;

         } else if (paymentOffered == PAYMENT_AMOUNT && terms == TERMS_AGREED) {
            __CPROVER_assert(p_at_gateway, "CWP: taking both agreed path requires p_at_gateway");
            __CPROVER_assert(p_negotiate, "CWP: taking both agreed path requires p_negotiate");
            __CPROVER_assert(p_terms_ready, "CWP: taking both agreed path requires p_terms_ready");
            __CPROVER_assert(p_price_ready, "CWP: taking both agreed path requires p_price_ready");
            /* Flow_0yqye0v: both agreed → proceed to shake hands */
            __CPROVER_assert(terms == TERMS_AGREED && paymentOffered == PAYMENT_AMOUNT,
                              "CWP: Purchase Agreed — terms and payment both satisfied");
            p_handshake = true;

         } else if (paymentOffered == NO_RETRY_PAYMENT || terms == TERMS_NO_RETRY) {
            /* Flow_0diuub0: noRetry condition → Purchase Failed */
            __CPROVER_assert(paymentOffered == NO_RETRY_PAYMENT || terms == TERMS_NO_RETRY,
                           "CWP: Purchase Failed — noRetry condition reached");
            p_failed = true;

         } else if (paymentOffered < PAYMENT_AMOUNT) {
            /* Flow_0q6dz8p: price below agreed amount → Task 4: repeat price negotiation
               Contract: paymentOffered becomes one of three values (non-det, noRetryPayment now possible) */
            int rp = nondet_int();
            __CPROVER_assume(rp == PAYMENT_AMOUNT ||
                           rp == BELOW_PAYMENT_AMOUNT ||
                           rp == NO_RETRY_PAYMENT);
            paymentOffered = rp;
            p_at_gateway   = true;

         } else {
            /* Flow_0koz64j: terms failed (price is fine) → Task 5: repeat terms negotiation
               Contract: terms becomes one of three values (non-det, noRetry now possible) */
            int rt = nondet_int();
            __CPROVER_assume(rt == TERMS_AGREED ||
                           rt == TERMS_FAILED  ||
                           rt == TERMS_NO_RETRY);
            terms        = rt;
            p_at_gateway = true;
         }
      }
   }

   /* ── Success path: exchange ownership ── */
   if (p_handshake) {
      /* Task 6: Buyer and Seller shake hands (no state change — coordination only) */
      p_handshake = false;
      p_exchange  = true;

      /* Parallel split "both1" (Gateway_000lymc):
         Dispatches Tasks 7a and 7b concurrently — serialized here.
         Unlike the negotiation tasks, these have deterministic contracts. */
      p_exchange = false;

      /* Task 7a: Buyer hands cash payment to Seller
         Contract: paymentOwner = sellerName (deterministic) */
      paymentOwner = SELLER_NAME;
      p_cash_done  = true;

      /* Task 7b: Seller hands Backpack to Buyer
         Contract: backpackOwner = buyerName (deterministic) */
      backpackOwner = BUYER_NAME;
      p_pack_done   = true;

      /* Parallel join "end both1" (Gateway_0cy7rs7): both exchanges complete */
      p_cash_done = false;
      p_pack_done = false;
      p_success   = true;

      /* CWP assertion: Ownerships Switched
         paymentOwner == sellerName && backpackOwner == buyerName */
      __CPROVER_assert(paymentOwner == SELLER_NAME && backpackOwner == BUYER_NAME,
                        "CWP: Ownerships Switched — seller has payment, buyer has backpack");
   }

   /* ── Failure path ── */
   if (p_failed) {
      /* CWP assertion: Purchase Failed terminal condition holds at termination */
      __CPROVER_assert(paymentOffered == NO_RETRY_PAYMENT || terms == TERMS_NO_RETRY,
                        "CWP: Purchase Failed — noRetry condition holds at termination");
   }

   return 0;
}
