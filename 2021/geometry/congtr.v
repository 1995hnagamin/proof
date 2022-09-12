(** congtr.v *)

Require Import Coq.Classes.Equivalence.


(* Group I. *)

Axiom Point: Type.

Axiom Line: Type.

Axiom EqL: Line -> Line -> Prop.

Axiom EqL_Equiv: Equivalence EqL.

Axiom Incid: Point -> Line -> Prop.

Axiom Incid_morphism: forall P l m,
    Incid P l -> EqL l m -> Incid P m.

Axiom Incid_dec: forall P l,
    Incid P l \/ ~Incid P l.

Axiom eq_dec_pointsH: forall A B: Point,
    A = B \/ A <> B.

(* Postulate I.1 *)
Axiom line_existence: forall A B,
    A <> B -> exists l, Incid A l /\ Incid B l.

(* Postulate I.2 *)
Axiom line_uniqueness: forall A B l m,
    A <> B ->
    Incid A l -> Incid B l ->
    Incid A m -> Incid B m ->
    EqL l m.

(* Postulate I.3 *)
Axiom two_points_on_line: forall l,
    { A: Point & { B | Incid B l /\ Incid A l /\ A <> B } }.

Definition ColH A B C :=
  exists l, Incid A l /\ Incid B l /\ Incid C l.

(* Postulate I.4 *)
Axiom l0: Line.
Axiom P0: Point.
Axiom lower_dim: ~ Incid P0 l0.



(* Group II. *)

Axiom BetH: Point -> Point -> Point -> Prop.

Axiom between_diff: forall A B C,
    BetH A B C -> A <> C.

(* Postulate II.1, collinearity *)
Axiom between_col: forall A B C,
    BetH A B C -> ColH A B C.

(* Postulate II.1, commucommutativity *)
Axiom between_comm: forall A B C,
    BetH A B C -> BetH C B A.

(* Postulate II.2 *)
Axiom between_out: forall A B,
    A <> B -> exists C, BetH A B C.

(* Postulate II.3 *)
Axiom between_only_one: forall A B C,
    BetH A B C -> ~BetH B C A.

Definition cut l A B :=
  ~Incid A l /\ ~Incid B l /\ exists I, Incid I l /\ BetH A I B.

(* Postulate II.4 *)
Axiom pasch: forall A B C l,
    ~ColH A B C -> ~Incid C l -> cut l A B -> cut l A C \/ cut l B C.



(* Group III. *)

Axiom CongH: Point -> Point -> Point -> Point -> Prop.

Axiom conf_permr: forall A B C D,
    CongH A B C D -> CongH A B D C.

Definition outH P A B :=
  BetH P A B \/ BetH P B A \/ (P <> A /\ A = B).

(* Postulate III.1 *)
Axiom cong_existence:
  forall A B A' P l,
    A <> B -> A' <> P -> Incid A' l -> Incid P l ->
    exists B', Incid B' l /\ outH A' P B' /\ CongH A' B' A B.

(* Postulate III.2 *)
Axiom cong_pseudo_transitivity:
  forall A B C D E F,
    CongH A B C D -> CongH A B E F -> CongH C D E F.

Definition disjoint A B C D :=
  ~exists P, BetH A P B /\ BetH C P D.

(* Postulate III.3 *)
Axiom addition: forall A B C A' B' C',
    ColH A B C -> ColH A' B' C' ->
    disjoint A B B C -> disjoint A' B' B' C' ->
    CongH A B A' B' -> CongH B C B' C' ->
    CongH A C A' C'.

Axiom CongaH: Point -> Point -> Point -> Point -> Point -> Point -> Prop.

Axiom conga_refl: forall A B C,
    ~ColH A B C -> CongaH A B C A B C.

Axiom conga_comm: forall A B C,
    ~ColH A B C -> CongaH A B C C B A.

Axiom congaH_permlr: forall A B C D E F,
    CongaH A B C D E F -> CongaH C B A F E D.

Definition same_side A B l := exists P, cut l A P /\ cut l B P.

Definition same_side' A B X Y :=
  X <> Y /\ forall l, Incid X l -> Incid Y l -> same_side A B l.

Axiom congaH_outH_congaH: forall A B C D E F A' C' D' F',
    CongaH A B C D E F ->
    outH B A A' -> outH B C C' ->
    outH E D D' -> outH E F F' ->
    CongaH A' B C' D' E F'.

Axiom cong_4_existence: forall A B C O X P,
    ~ColH P O X -> ~ColH A B C ->
    exists Y, CongaH A B C X O Y /\ same_side' P Y O X.

Axiom cong_4_uniqueness: forall A B C O P X Y Y',
    ~ColH P O X -> ~ColH A B C ->
    CongaH A B C X O Y -> CongaH A B C X O Y' ->
    same_side' P Y O X -> same_side' P Y' O X ->
    outH O Y Y'.

(* Postulate III.5 *)
Axiom cong_5: forall A B C A' B' C',
    ~ColH A B C -> ~ColH A' B' C' ->
    CongH A B A' B' -> CongH A C A' C' ->
    CongaH B A C B' A' C' ->
    CongaH A B C A' B' C'.



(* Congruence of triangles *)

Definition Cong_3 A B C A' B' C' :=
  CongH A B A' B' /\ CongH B C B' C' /\ CongH C A C' A'.

Proposition sas_congr: forall A B C A' B' C',
    CongH A B A' B' -> CongaH A B C A' B' C' -> CongH B C B' C' ->
    Cong_3 A B C A' B' C'.
Proof.
  intros A B C A' B' C' Hab Hang Hbc. unfold Cong_3.
  split. apply Hab.
  split. apply Hbc.
  apply (addition )
