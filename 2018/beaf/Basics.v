Require Import Omega.

Module Beaf.

  Notation "a ^ b" := (Nat.pow a b) (right associativity, at level 30).

  Example power_example1 :
    2 ^ 2 ^ 3 = 256.
  Proof.
    reflexivity.
  Qed.

  Definition googol := 10 ^ 100.
  Definition googolplex := 10 ^ googol.

  Fixpoint tetration (a:nat) (b:nat) : nat :=
    match b with
    | O => 1
    | S b' => a ^ (tetration a b')
    end.

  Notation "a ^^ b" := (tetration a b) (right associativity, at level 30).

  Inductive arrowR : nat -> nat -> nat -> nat -> Prop :=
  | ArrowBaseN : forall a b,
      arrowR a 1 b (a ^ b)
  | ArrowBaseRhs : forall a n,
      arrowR a (S n) 0 1
  | ArrowInd : forall a b n x y,
      arrowR a (S n) b y ->
      arrowR a n y x ->
      arrowR a (S n) (S b) x.

  Notation "[ a ^{ n } b == x ]" := (arrowR a n b x) (at level 100).

  Lemma arrowR_0 : forall a b x,
      ~ [a ^{0} b == x].
  Proof.
    intros a b x E. inversion E.
  Qed.

  Proposition arrowR_eq_x : forall a n b x x',
      [a ^{n} b == x] -> [a ^{n} b == x'] -> x = x'.
  Proof.
    intros a n b x x' Hx Hx'.
    generalize dependent x'.
    induction Hx; intros x' Hx';
      inversion Hx'; subst; try reflexivity.
    - (* ArrowInd *)
      apply IHHx2. replace y with y0. assumption.
      symmetry. apply IHHx1. assumption.
  Qed.

  Proposition arrowR_exists_x : forall a n b,
      exists x, [a ^{n} b == x].
  Proof.
    intros a n.
    induction n as [| n' IHn']; intros b.
    - exists (a ^ b). apply ArrowBaseN. reflexivity.
    - induction b as [| b' IHb'].
      + exists a. apply ArrowBaseRhs. reflexivity.
      + destruct IHb' as [y IHb'].
        specialize (IHn' y). destruct IHn' as [x IHn'].
        exists x. apply ArrowInd with y; assumption.
  Qed.

  Example tetration_arrowR2_equiv : forall a b,
      [a ^{_2_} b == a ^^ b].
  Proof.
    intros a b. induction b as [|b' IHb'].
    - (* b = 1 *)
      simpl. apply ArrowBaseRhs. reflexivity.
    - (* b > 1 *)
      inversion IHb'; subst.
      + simpl. eapply ArrowInd.
        apply ArrowBaseRhs. reflexivity.
        apply ArrowBaseN. reflexivity.
      + eapply ArrowInd.
        apply IHb'.
        apply ArrowBaseN. reflexivity.
  Qed.

End Beaf.
