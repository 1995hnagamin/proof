Require Import Coq.Lists.List.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Omega.

Module QuickSort.

  Import ListNotations.

  Check filter.

  Lemma filter_lt : forall (A:Type) pred (l:list A),
      length (filter pred l) <= length (filter pred l).
  Proof.
    intros. induction l as [| x l' IHl'].
    - simpl. omega.
    - simpl. destruct (pred x).
      + simpl. apply le_n_S. assumption.
      + constructor.
  Qed.

  Lemma lt_def : forall n m,
      S n <= m <-> n < m.
  Proof.
    intros n m. omega.
  Qed.

  Program Fixpoint qsort (l:list nat) {measure (length l)}
    : list nat :=
    match l with
    | [] => []
    | x :: xs =>
      let lt : list nat := filter (fun n:nat => Nat.ltb n x) xs in
      let ge : list nat := filter (fun n:nat => Nat.leb x n) xs in
      (qsort lt) ++ [x] ++ (qsort ge)
    end.
  Next Obligation.
    induction xs as [| x' xs' IHxs'].
    - (* xs = [ ] *)
      simpl. omega.
    - (* xs = x' :: xs' *)
      simpl. destruct (x' <? x) eqn:Hbool.
      + simpl. apply lt_n_S. replace (S (length xs')) with (length (x::xs')).
        apply IHxs'. intros l Hl. apply xs'.
        simpl. omega.
      + constructor. apply lt_def. apply IHxs'.
        intros l H. apply xs'.
  Qed.
  Next Obligation.
    induction xs as [| x' xs' IHxs'].
    - simpl. omega.
    - simpl. destruct (x <=? x') eqn:Hbool.
      + simpl. apply lt_n_S. replace (S (length xs')) with (length (x::xs')).
        apply IHxs'. intros l Hl. apply xs'.
        reflexivity.
      + apply le_S. replace (S (length xs')) with (length (x::xs')).
        apply lt_def. apply IHxs'. intros l Hl. apply xs'.
        reflexivity.
  Qed.

End QuickSort.
