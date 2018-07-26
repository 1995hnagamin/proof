(** Prop.v *)

Definition dbl_neg (P:Prop) :=
  ~~P -> P.

Proposition nndn : forall P,
    ~~(dbl_neg P).
Proof.
  intros P NDN.
  apply NDN. intros DNP.
  exfalso. apply DNP. intros HP. apply NDN. intros DNP2. exact HP.
Qed.

Proposition nnadn :
  ~~(forall P, dbl_neg P).
Proof.
  intros NADN. apply NADN. intros P.
  intros NNP.
Abort.

Proposition tn : forall P,
    dbl_neg (~P).
Proof.
  intros P TN HP. apply TN. intros NP. apply NP. exact HP.
Qed.

Definition excl_mid (P:Prop) :=
  P \/ ~P.

Proposition nnem : forall P,
    ~~(excl_mid P).
Proof.
  intros P NEM. apply NEM.
  right. intros HP. apply NEM.
  left. exact HP.
Qed.

Proposition nnaem :
  ~~(forall P, excl_mid P).
Proof.
  intros NAEM. apply NAEM.
  intros P. right. intros HP.
  apply NAEM. intros P'. 
Abort.

Proposition em2dn : forall P,
    (excl_mid P) -> (dbl_neg P).
Proof.
  intros P EMP NNP. destruct EMP as [HP | NP].
  - apply HP.
  - exfalso. apply NNP. exact NP.
Qed.

Proposition dn2em : forall P,
    (dbl_neg P) -> (excl_mid P).
Proof.
  intros P DN.
Abort.

Proposition adn_eq_aem :
    (forall P, dbl_neg P) <-> (forall P, excl_mid P).
Proof.
  split.
  - (* -> *)
    intros ADN P. apply ADN. intros NEM. apply NEM.
    left. apply ADN. intros NP. apply NEM.
    right. exact NP.
  - (* <- *)
    intros AEM P. apply em2dn. apply AEM.
Qed.

Definition pierce (P Q:Prop) :=
  ((P -> Q) -> P) -> P.

Proposition nn_pierce : forall P Q : Prop,
    ~~(pierce P Q).
Proof.
  intros P Q NPQPP. apply NPQPP.
  intros PQP. apply PQP.
  intros HP. exfalso.
  apply NPQPP. intros ?. exact HP.
Qed.

Proposition dn_eq_pierce : forall P Q,
    (dbl_neg P) <-> (pierce P Q).
Proof.
  split.
  - (* -> *)
    intros DN PQP. apply DN.
    intros NP. apply NP. apply PQP.
    intros HP. congruence.
  - (* <- *)
    intros PQPP NNP. apply PQPP.
    intros PQ. Abort.

Proposition adn_eq_apierce :
  (forall P, dbl_neg P) <-> (forall P Q, pierce P Q).
Proof.
  split.
  - (* -> *)
    intros ADN P Q PQP.
    apply ADN. intros NP. apply NP. apply PQP. intros HP.
    congruence.
  - (* <- *)
    intros APQPP P NNP. apply APQPP with False. intros NP.
    exfalso. apply NNP. exact NP.
Qed.

Corollary aem_eq_apierce :
  (forall P, excl_mid P) <-> (forall P Q, pierce P Q).
Proof.
  eapply iff_trans.
  - apply iff_sym. apply adn_eq_aem.
  - apply adn_eq_apierce.
Qed.

Proposition adn_eq_aqpierce : forall P,
    (dbl_neg P) <-> (forall Q, pierce P Q).
Proof.
  split.
  - (* -> *)
    intros DN Q PQP. apply DN. intros NP. apply NP.
    apply PQP. intros HP. congruence.
  - (* <- *)
    intros HPQ NNP. apply HPQ with False.
    intros NP. exfalso. apply NNP. exact NP.
Qed.

(* Reductio ad absurdum *)
Definition red_absurd (P:Prop) :=
  (~P -> P) -> P.
