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
    intros a n b x x' Ex Ex'.
    generalize dependent x'.
    induction Ex; intros x' Ex';
      inversion Ex'; subst; try reflexivity.
    - (* contradiction *)
      exfalso. eapply arrowR_0. apply H2.
    - exfalso. eapply arrowR_0. apply Ex2.
    - apply IHEx2. replace y with y0. assumption.
      symmetry. apply IHEx1. assumption.
  Qed.

  Proposition arrowR_exists_x : forall a n b,
      exists x, [a ^{S n} b == x].
  Proof.
    intros a n.
    induction n as [| n' IHn']; intros b.
    - exists (a ^ b). apply ArrowBaseN.
    - induction b as [| b' IHb'].
      + (* b = 0 *)
        exists 1. constructor.
      + (* b > 0 *)
        destruct IHb' as [y IHb'].
        specialize (IHn' y). destruct IHn' as [x IHn'].
        exists x. apply ArrowInd with y.
        assumption. assumption.
  Qed.

  Example tetration_arrowR2_equiv : forall a b,
      [a ^{2} b == a ^^ b].
  Proof.
    intros a b. induction b as [|b' IHb'].
    - (* b = 0 *)
      simpl. apply ArrowBaseRhs.
    - (* b > 0 *)
      inversion IHb'; subst.
      + simpl. eapply ArrowInd.
        apply ArrowBaseRhs. apply ArrowBaseN.
      + eapply ArrowInd.
        apply IHb'.
        apply ArrowBaseN.
  Qed.

End Beaf.
