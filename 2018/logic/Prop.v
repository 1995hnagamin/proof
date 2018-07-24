(** Prop.v *)

Proposition nndn : forall P,
    ~~(~~P -> P).
Proof.
  intros P NDN.
  apply NDN. intros DNP.
  exfalso. apply DNP. intros HP. apply NDN. intros DNP2. exact HP.
Qed.

Proposition nnadn :
  ~~(forall P, ~~P -> P).
Proof.
  intros NADN. apply NADN. intros P.
  intros NNP.
Abort.

Proposition tn : forall P,
    ~~~P -> ~P.
Proof.
  intros P TN HP. apply TN. intros NP. apply NP. exact HP.
Qed.

Proposition nnem : forall P,
    ~~(P \/ ~P).
Proof.
  intros P NEM. apply NEM.
  right. intros HP. apply NEM.
  left. exact HP.
Qed.

Proposition nnaem :
  ~~(forall P, P \/ ~P).
Proof.
  intros NAEM. apply NAEM.
  intros P. right. intros HP.
  apply NAEM. intros P'. 
Abort.

Proposition em2dn : forall P,
    (P \/ ~P) -> (~~P -> P).
Proof.
  intros P EMP NNP. destruct EMP as [HP | NP].
  - apply HP.
  - exfalso. apply NNP. exact NP.
Qed.

Proposition dn2em : forall P,
    (~~P -> P) -> (P \/ ~P).
Proof.
  intros P DN.
Abort.

Proposition adn_eq_aem :
    (forall P, ~~P -> P) <-> (forall P, P \/ ~P).
Proof.
  split.
  - (* -> *)
    intros ADN P. apply ADN. intros NEM. apply NEM.
    left. apply ADN. intros NP. apply NEM.
    right. exact NP.
  - (* <- *)
    intros AEM P. apply em2dn. apply AEM.
Qed.
