(** naimonowanai. v *)

Definition aru {T: Type} (x: T) : Prop :=
  exists y, x = y.

Example ex1: aru 1.
Proof.
  unfold aru. exists 1. reflexivity.
Qed.

Definition nai {T: Type} (x: T) : Prop :=
  ~ (aru x).

Theorem nai_nara_nai: forall (T: Type) (x: T),
    nai x -> nai x.
Proof.
  intros T x Hnai. apply Hnai.
Qed.

Theorem nai_monowa_sonzai_sinai: forall (T: Type),
    ~ (exists (x: T), nai x).
Proof.
  intros T contra.
  destruct contra as [x Hnai].
  apply Hnai.
  unfold aru. exists x. reflexivity.
Qed.

Theorem subetewa_aru: forall (T: Type) (x: T),
    aru x.
Proof.
  intros T x. exists x. reflexivity.
Qed.

