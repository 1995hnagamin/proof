Module Beaf.

  Inductive pint : Type :=
  | I : pint
  | S : pint -> pint.

  Fixpoint plus (a:pint) (b:pint) : pint :=
    match b with
    | I => S a
    | S b' => S (plus a b')
    end.

  Fixpoint mult (a:pint) (b:pint) : pint :=
    match b with
    | I => a
    | S b' => plus a (mult a b')
    end.

  Fixpoint power (a:pint) (b:pint) : pint :=
    match b with
    | I => a
    | S b' => mult a (power a b')
    end.

  Notation "a + b" := (plus a b) (left associativity, at level 50).
  Notation "a * b" := (mult a b) (left associativity, at level 40).
  Notation "a ^ b" := (power a b) (right associativity, at level 30).

  Lemma plus_S_n : forall a b,
      (S a) + b = S (a + b).
  Proof.
    intros a b. generalize dependent a.
    induction b as [| b' IHb']; intros a.
    - reflexivity.
    - simpl. rewrite IHb'. reflexivity.
  Qed.

  Lemma plus_assoc : forall a b c,
      (a + b) + c = a + (b + c).
  Proof.
    intros a b c. induction c as [|c' IHc'].
    - reflexivity.
    - simpl. rewrite IHc'. reflexivity.
  Qed.

  Lemma plus_comm : forall a b,
      a + b = b + a.
  Proof.
    intros a. induction a as [|a' IHa']; intros b.
    - induction b as [|b' IHb'].
      + reflexivity.
      + simpl. rewrite IHb'. reflexivity.
    - simpl. rewrite <- IHa'. rewrite plus_S_n. reflexivity.
  Qed.

  Lemma pint_distributive : forall a b c,
      a * (b + c) = a * b + a * c.
  Proof.
    intros a b c. induction c as [| c' IHc'].
    - simpl. rewrite plus_comm. reflexivity.
    - simpl. rewrite IHc'.
      replace (a + (a * b + a * c')) with ((a + a * b) + a * c').
      replace (a + a * b) with (a * b + a).
      apply plus_assoc. apply plus_comm. apply plus_assoc.
  Qed.

  Lemma mult_assoc : forall a b c,
      (a * b) * c = a * (b * c).
  Proof.
    intros a b c. induction c as [|c' IHc'].
    - reflexivity.
    - simpl. rewrite pint_distributive. rewrite <- IHc'. reflexivity.
  Qed.

  Lemma mult_S_n : forall a b,
      (S a) * b = a * b + b.
  Proof.
    intros a b. induction b as [| b' IHb'].
    - reflexivity.
    - simpl. rewrite IHb'. rewrite plus_S_n.
      rewrite plus_assoc. reflexivity.
  Qed.

  Lemma mult_comm : forall a b,
      a * b = b * a.
  Proof.
    intros a. induction a as [| a' IHa'].
    - intros b. induction b as [| b' IHb'].
      + reflexivity.
      + simpl. rewrite IHb'. rewrite plus_comm. reflexivity.
    - intros b. rewrite mult_S_n. simpl. rewrite IHa'.
      rewrite plus_comm. reflexivity.
  Qed.

  Definition _2_ := S I.
  Definition _3_ := S _2_.

  Fixpoint to_nat (a:pint) : nat :=
    match a with
    | I => 1
    | S a' => (to_nat a') + 1
    end.

  Example example1 :
    to_nat (_2_ ^ _2_ ^ _3_) = 256.
  Proof.
    simpl. reflexivity.
  Qed.

  Fixpoint tetration (a:pint) (b:pint) : pint :=
    match b with
    | I => a
    | S b' => power a (tetration a b')
    end.

  Notation "a ^^ b" := (tetration a b) (right associativity, at level 30).

  Inductive arrowR : pint -> pint -> pint -> pint -> Prop :=
  | ArrowBaseN : forall a b x,
      x = a ^ b -> arrowR a I b x
  | ArrowBaseRhs : forall a n x,
      a = x -> arrowR a n I x
  | ArrowInd : forall a b n x y,
      arrowR a (S n) b y ->
      arrowR a n y x ->
      arrowR a (S n) (S b) x.

  Notation "[ a ^{ n } b == x ]" := (arrowR a n b x) (at level 100).

  Lemma arrowR_eq_x : forall a n b x x',
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

  Lemma arrowR_exists_x : forall a n b,
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
