Require Import Nat.
Require Import ZArith.
Require Import Lia.


Theorem thm1: forall n m,
 n <= m -> exists k, n + k = m.
intros n m H. generalize dependent n.
induction m as [| m' IH].
- intros n H. inversion H.
  exists 0. lia.
- intros n H.
  inversion H.
  exists 0. lia.
  apply IH in H1. destruct H1 as [k H1].
  exists (S k). lia.
Qed.
