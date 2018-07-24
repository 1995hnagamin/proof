(** Quant.v *)

Proposition ap2nenp : forall (T: Type) (P: T -> Prop),
    (forall x, P x) -> ~(exists x, ~(P x)).
Proof.
  unfold not. intros T P H1 H2.
  destruct H2 as [x H2]. apply H2. apply H1.
Qed.

Proposition anp2nep : forall (T: Type) (P: T -> Prop),
    (forall x, ~(P x)) -> ~(exists x, P x).
Proof.
  unfold not. intros T P H1 H2.
  destruct H2 as [x H2]. eapply H1. apply H2.
Qed.

Proposition ep2nanp : forall (T: Type) (P: T -> Prop),
    (exists x, P x) -> ~(forall x, ~(P x)).
Proof.
  unfold not. intros T P [x H1] H2.
  eapply H2. apply H1.
Qed.

Proposition enp2nap : forall (T: Type) (P: T -> Prop),
    (exists x, ~(P x)) -> ~(forall x, P x).
Proof.
  unfold not. intros T P [x H1] H2.
  apply H1. apply H2.
Qed.

Proposition nenp2ap : forall (T: Type) (P: T -> Prop),
    ~(exists x, ~(P x)) -> forall x, P x.
Proof.
  unfold not. intros T P H1 x.
Abort.
