(** Prop.v *)

Proposition nndn : forall P,
    ~~(~~P -> P).
Proof.
  intros P NDN.
  apply NDN. intros DNP.
  exfalso. apply DNP. intros HP. apply NDN. intros DNP2. exact HP.
Qed.

Proposition tn : forall P,
    ~~~P -> ~P.
Proof.
  intros P TN HP. apply TN. intros NP. apply NP. exact HP.
Qed.
