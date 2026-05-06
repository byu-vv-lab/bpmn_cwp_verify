/*
 * face2face_strate_v2.st — face2face with explicit parallel interleaving
 *
 * AND-split/join modeled with `if *`: non-deterministically orders parallel
 * tasks so Strata proves assertions hold under every possible ordering.
 *
 * lake exe strata verify face2face_strate_v2.st
 */

program Core;

procedure face2faceVerify (inout terms: int, inout backpackOwner: int,
                           inout paymentOwner: int, inout paymentOffered: int)
spec {
  requires (terms == 2);            // TERMS_PENDING
  requires (backpackOwner == 1);    // SELLER_NAME
  requires (paymentOwner == 0);     // BUYER_NAME
  requires (paymentOffered == 255); // PENDING_PAYMENT
}
{
  var agreed : bool := false;
  var failed : bool := false;

  backpackOwner := 1;
  paymentOwner  := 0;
  assert [init_state]: (paymentOwner == 0 && backpackOwner == 1);

  while (!agreed && !failed)
    invariant (paymentOwner == 0)
    invariant (backpackOwner == 1)
    invariant (!(agreed && failed))
  {
    // AND-split: Task 2 and Task 3 are parallel — `if *` picks the ordering
    if * {
      if * {
        terms := 0;
      } else {
        if * {
          terms := 1;
        } else {
          terms := 3;
        }
      }
      if * {
        paymentOffered := 253;
      } else {
        if * {
          paymentOffered := 252;
        } else {
          paymentOffered := 254;
        }
      }
    } else {
      if * {
        paymentOffered := 253;
      } else {
        if * {
          paymentOffered := 252;
        } else {
          paymentOffered := 254;
        }
      }
      if * {
        terms := 0;
      } else {
        if * {
          terms := 1;
        } else {
          terms := 3;
        }
      }
    }
    // AND-join: both tasks complete before the gateway

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

  if (agreed) {
    // AND-split: Task 7a and Task 7b are parallel
    if * {
      paymentOwner  := 1;
      backpackOwner := 0;
    } else {
      backpackOwner := 0;
      paymentOwner  := 1;
    }
    // AND-join
    assert [ownerships_switched]: (paymentOwner == 1 && backpackOwner == 0);
  }

  if (failed) {
    assert [purchase_failed_terminal]: (paymentOffered == 254 || terms == 3);
  }
};
