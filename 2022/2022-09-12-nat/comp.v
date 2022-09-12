Require Import Nat.
Require Import PeanoNat.

Theorem thm1: forall n m :nat,
  (n <> m) -> n < m \/ m < n.
Proof.
  intros n m H.
  case_eq (n ?= m); intros Hcomp.
  - (* Eq *)
    exfalso. apply H.
    apply Nat.compare_eq_iff.
    assumption.
  - left. apply Nat.compare_lt_iff.
    assumption.
  - right. apply Nat.compare_gt_iff.
    assumption.
Qed.
