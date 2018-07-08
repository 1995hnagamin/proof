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

  Definition p2 := S I.
  Definition p3 := S p2.

  Fixpoint to_nat (a:pint) : nat :=
    match a with
    | I => 1
    | S a' => (to_nat a') + 1
    end.

  Example example1 :
    to_nat (p2 ^ p2 ^ p3) = 256.
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
    induction Hx; intros x' Hx'.
    - (* n = 1 *)
      inversion Hx'; subst; reflexivity.
    - (* b = 1 *)
      inversion Hx'; subst; reflexivity.
    - (* ArrowInd *)
      inversion Hx'; subst.
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

End Beaf.
