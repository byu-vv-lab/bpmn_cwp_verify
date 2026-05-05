#include <stdbool.h>

int nondet_int();

/* TermsType */
#define TERMS_AGREED   0
#define TERMS_FAILED   1
#define TERMS_PENDING  2
#define TERMS_NO_RETRY 3

/* OwnerType */
#define BUYER_NAME  0
#define SELLER_NAME 1

/* paymentOffered values */
#define PAYMENT_AMOUNT       253
#define BELOW_PAYMENT_AMOUNT 252
#define NO_RETRY_PAYMENT     254
#define PENDING_PAYMENT      255

int main() {
   int terms          = TERMS_PENDING;
   int backpackOwner  = SELLER_NAME;
   int paymentOwner   = BUYER_NAME;
   int paymentOffered = PENDING_PAYMENT;

   bool agreed = false;
   bool failed = false;

   /* Task 1: establish initial ownership */
   backpackOwner = SELLER_NAME;
   paymentOwner  = BUYER_NAME;
   __CPROVER_assert(paymentOwner == BUYER_NAME && backpackOwner == SELLER_NAME,
                    "CWP: Init Purchase Pending");

   /* Negotiation loop — bound via --unwind N on the command line */
   while (!agreed && !failed) {

      /* Task 2: negotiate terms — terms ∈ {agreed, failed, noRetry} */
      int t = nondet_int();
      __CPROVER_assume(t == TERMS_AGREED || t == TERMS_FAILED || t == TERMS_NO_RETRY);
      terms = t;

      /* Task 3: negotiate price — paymentOffered ∈ {amount, below, noRetry} */
      int p = nondet_int();
      __CPROVER_assume(p == PAYMENT_AMOUNT || p == BELOW_PAYMENT_AMOUNT || p == NO_RETRY_PAYMENT);
      paymentOffered = p;

      /* Gateway: decide outcome */
      if (terms == TERMS_AGREED && paymentOffered == PAYMENT_AMOUNT) {
         __CPROVER_assert(terms == TERMS_AGREED && paymentOffered == PAYMENT_AMOUNT,
                          "CWP: Purchase Agreed");
         agreed = true;
      } else if (terms == TERMS_NO_RETRY || paymentOffered == NO_RETRY_PAYMENT) {
         __CPROVER_assert(terms == TERMS_NO_RETRY || paymentOffered == NO_RETRY_PAYMENT,
                          "CWP: Purchase Failed");
         failed = true;
      }
      /* else: still negotiating — loop continues */
   }

   /* Success path: Tasks 7a + 7b exchange ownership */
   if (agreed) {
      paymentOwner  = SELLER_NAME;
      backpackOwner = BUYER_NAME;
      __CPROVER_assert(paymentOwner == SELLER_NAME && backpackOwner == BUYER_NAME,
                       "CWP: Ownerships Switched");
   }

   /* Failure path */
   if (failed) {
      __CPROVER_assert(paymentOffered == NO_RETRY_PAYMENT || terms == TERMS_NO_RETRY,
                       "CWP: Purchase Failed terminal");
   }

   return 0;
}
