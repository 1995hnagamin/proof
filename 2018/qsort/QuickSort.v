Require Import Coq.Lists.List.
Require Import Coq.Program.Tactics.
Require Import Coq.Program.Wf.
Require Import Omega.

Import ListNotations.

Inductive sorted : list nat -> Prop :=
| SortedEmpty : sorted [ ]
| SortedSingleton : forall n, sorted [n]
| SortedInd : forall n m l,
    n <= m -> sorted (m :: l) -> sorted (n :: m :: l).

Module HeapSort.

  Inductive bintree : Type :=
  | Leaf : nat -> bintree
  | Inner : nat -> bintree -> bintree -> bintree.

  Fixpoint height (t:bintree) : nat :=
    match t with
    | Leaf _ => 0
    | Inner _ c1 c2 => S (Nat.max (height c1) (height c2))
    end.

  Fixpoint vertices (t:bintree) : nat :=
    match t with
    | Leaf _ => 1
    | Inner _ c1 c2 => (vertices c1) + (vertices c2) + 1
    end.

  Definition root (t:bintree) : nat :=
    match t with
    | Leaf n => n
    | Inner n _ _ => n
    end.

  Inductive perfect : bintree -> Prop :=
  | PerfectSingleton : forall n,
      perfect (Leaf n)
  | PerfectInd : forall n t1 t2,
      perfect t1 ->
      perfect t2 ->
      height t1 = height t2 ->
      perfect (Inner n t1 t2).

  Lemma sum_pos : forall a b,
      a > 0 -> a + b > 0.
  Proof.
    intros a b. omega.
  Qed.

  Lemma product_pos : forall a b,
      a > 0 -> b > 0 -> a * b > 0.
  Proof.
    intros a b Ha. induction b as [| b' IHb' ].
    - intros Hb. inversion Hb.
    - intros Hb. replace (a * S b') with (a + a * b').
      apply sum_pos. assumption.
      (* a * S b' = a + a * b' *) rewrite <- mult_n_Sm. omega.
  Qed.

  Lemma pow_pos : forall a n,
      a > 0 -> a ^ n > 0.
  Proof.
    intros a n H. induction n as [| n' IHn' ].
    - simpl. omega.
    - simpl. remember (a ^ n') as k. apply product_pos.
      assumption. assumption.
  Qed.

  Proposition vertices_of_perfect_bintree : forall t,
      perfect t ->
      vertices t = (Nat.pow 2 (height t + 1)) - 1.
  Proof.
    intros t E. induction E.
    - (* PerfectSingleton *)
      reflexivity.
    - (* PerfectInd *)
      simpl. replace (height t2) with (height t1).
      rewrite max_l. replace (vertices t2) with (vertices t1).
      rewrite IHE1.
      assert (Lem: 2 ^ (height t1 + 1) > 0).
      { apply pow_pos. omega. }
      remember (2 ^ (height t1 + 1)) as k. omega.
      (* vertices t1 = vertices t2 *)
      rewrite IHE1. rewrite IHE2. rewrite H. reflexivity.
      (* height t1 <= height t2 *) omega.
  Qed.

  Inductive complete : bintree -> Prop :=
  | CompleteSingleton : forall n,
      complete (Leaf n)
  | CompleteA : forall n t1 t2,
      height t1 = height t2 + 1 ->
      complete t1 ->
      perfect t2 ->
      complete (Inner n t1 t2)
  | CompleteB : forall n t1 t2,
      height t1 = height t2 ->
      perfect t1 ->
      complete t2 ->
      complete (Inner n t1 t2).

End HeapSort.

Module QuickSort.

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

  Example qsort_example :
    qsort [3; 1; 4; 1; 5; 9; 2] = [1; 1; 2; 3; 4; 5; 9].
  Proof.
    reflexivity.
  Qed.

End QuickSort.
