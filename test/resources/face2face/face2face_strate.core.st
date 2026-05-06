program Core;

procedure face2faceVerify (inout terms: int, inout backpackOwner: int,
                           inout paymentOwner: int, inout paymentOffered: int)
spec {
  requires (terms == 2);             // TERMS_PENDING
  requires (backpackOwner == 1);     // SELLER_NAME
  requires (paymentOwner == 0);      // BUYER_NAME
  requires (paymentOffered == 255);  // PENDING_PAYMENT
}
{
  var agreed : bool := false;
  var failed : bool := false;

  // Task 1: establish initial ownership
  backpackOwner := 1;
  paymentOwner  := 0;
  assert [init_state]: (paymentOwner == 0 && backpackOwner == 1);

  while (!agreed && !failed)
    invariant (paymentOwner == 0)
    invariant (backpackOwner == 1)
    invariant (!(agreed && failed))
  {
    // Task 2: negotiate terms — terms ∈ {agreed(0), failed(1), noRetry(3)}
    if * {
      terms := 0;
    } else {
      if * {
        terms := 1;
      } else {
        terms := 3;
      }
    }

    // Task 3: negotiate price — paymentOffered ∈ {amount(253), below(252), noRetry(254)}
    if * {
      paymentOffered := 253;
    } else {
      if * {
        paymentOffered := 252;
      } else {
        paymentOffered := 254;
      }
    }

    // Gateway: decide outcome
    if (terms == 0 && paymentOffered == 253) {
      assert [purchase_agreed]: (terms == 0 && paymentOffered == 253);
      agreed := true;
    } else {
      if (terms == 3 || paymentOffered == 254) {
        assert [purchase_failed]: (terms == 3 || paymentOffered == 254);
        failed := true;
      }
    }
  }

  // Success path: Tasks 7a + 7b exchange ownership
  if (agreed) {
    paymentOwner  := 1;  // buyer pays seller
    backpackOwner := 0;  // seller hands backpack to buyer
    assert [ownerships_switched]: (paymentOwner == 1 && backpackOwner == 0);
  }

  // Failure path
  if (failed) {
    assert [purchase_failed_terminal]: (paymentOffered == 254 || terms == 3);
  }
};
