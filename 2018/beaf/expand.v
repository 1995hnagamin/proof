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

End Beaf.
