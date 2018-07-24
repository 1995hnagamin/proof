(** Prop.v *)

Proposition nndn : forall P,
    ~~(~~P -> P).
Proof.
  intros P NDN.
  apply NDN. intros DNP.
  exfalso. apply DNP. intros HP. apply NDN. intros DNP2. apply HP.
Qed.
