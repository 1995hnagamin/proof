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
  | Left : nat -> bintree -> bintree
  | Right : nat -> bintree -> bintree
  | Fork : nat -> bintree -> bintree -> bintree.

  Fixpoint height (t:bintree) : nat :=
    match t with
    | Leaf _ => 0
    | Left _ c1 => S (height c1)
    | Right _ c2 => S (height c2)
    | Fork _ c1 c2 => S (Nat.max (height c1) (height c2))
    end.

  Fixpoint vertices (t:bintree) : nat :=
    match t with
    | Leaf _ => 1
    | Left _ c1 => S (vertices c1)
    | Right _ c2 => S (vertices c2)
    | Fork _ c1 c2 => (vertices c1) + (vertices c2) + 1
    end.

  Definition root (t:bintree) : nat :=
    match t with
    | Leaf n => n
    | Left n _ => n
    | Right n _ => n
    | Fork n _ _ => n
    end.

  Inductive perfect : bintree -> Prop :=
  | PerfectSingleton : forall n,
      perfect (Leaf n)
  | PerfectInd : forall n t1 t2,
      perfect t1 ->
      perfect t2 ->
      height t1 = height t2 ->
      perfect (Fork n t1 t2).

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

  Fixpoint perfb (t:bintree) : bool :=
    match t with
    | Leaf _ => true
    | Left _ _ => false
    | Right _ _ => false
    | Fork _ t1 t2 =>
      (height t1 =? height t2) && perfb t1 && perfb t2
    end.

  Proposition perfb_true_iff : forall t,
      perfect t <-> perfb t = true.
  Proof.
    intros t. split.
    - (* -> *)
      intros E. induction E.
      + (* t = Leaf n *)
        reflexivity.
      + (* t = Inner n t1 t2 *)
        simpl. rewrite H. rewrite IHE1. rewrite IHE2.
        replace (height t2 =? height t2) with true. reflexivity.
        (* goal: height t2 =? height t2 *) apply beq_nat_refl.
    - (* <- *)
      induction t as [n | n t1 | n t2 | n t1 IHt1 t2 IHt2].
      + intros. apply PerfectSingleton.
      + (* contradiction *) intros contra. inversion contra.
      + (* contradiciton *) intros contra. inversion contra.
      + intros H. simpl in H.
        apply andb_prop in H. destruct H as [H Ht2].
        apply andb_prop in H. destruct H as [Hheight Ht1].
        apply PerfectInd.
        * apply IHt1. apply Ht1.
        * apply IHt2. apply Ht2.
        * apply beq_nat_true_iff. apply Hheight.
  Qed.

  Inductive complete : bintree -> Prop :=
  | CompleteSingleton : forall n,
      complete (Leaf n)
  | CompleteLeft : forall n m,
      complete (Left n (Leaf m))
  | CompleteA : forall n t1 t2,
      height t1 = height t2 + 1 ->
      complete t1 ->
      perfect t2 ->
      complete (Fork n t1 t2)
  | CompleteB : forall n t1 t2,
      height t1 = height t2 ->
      perfect t1 ->
      complete t2 ->
      complete (Fork n t1 t2).

  Proposition perfect_imp_complete : forall t,
      perfect t -> complete t.
  Proof.
    intros t E. induction E.
    - (* PerfectSingleton *)
      apply CompleteSingleton.
    - (* PerfectInd *)
      apply CompleteB; assumption.
  Qed.

  Inductive sat_heap_prop : bintree -> Prop :=
  | SatHPSingle : forall n,
      sat_heap_prop (Leaf n)
  | SatHPLeft : forall n t1,
      sat_heap_prop t1 ->
      root t1 <= n ->
      sat_heap_prop (Left n t1)
  | SatHPRight : forall n t2,
      sat_heap_prop t2 ->
      root t2 <= n ->
      sat_heap_prop (Right n t2)
  | SatHPFork : forall n t1 t2,
      sat_heap_prop t1 ->
      sat_heap_prop t2 ->
      root t1 <= n ->
      root t2 <= n ->
      sat_heap_prop (Fork n t1 t2).

  Fixpoint max_vertex (t:bintree) : nat :=
    match t with
    | Leaf n => n
    | Left n t1 =>
      Nat.max n (max_vertex t1)
    | Right n t2 =>
      Nat.max n (max_vertex t2)
    | Fork n t1 t2 =>
      Nat.max n (Nat.max (max_vertex t1) (max_vertex t2))
    end.

  Lemma max_upper : forall a b m,
      a <= m -> b <= m -> Nat.max a b <= m.
  Proof.
    intros a b m Ea. generalize dependent b.
    induction Ea.
    - (* a = m *)
      intros b Eb. induction Eb.
      + (* b = a *)
        replace (Nat.max b b) with b. apply le_n.
        (* goal: b = Nat.max b b *)
        symmetry. apply max_l. apply le_n.
      + (* b <= m - 1 *)
        replace (Nat.max (S m) b) with (S m). apply le_n.
        (* goal: S m = Nat.max (S m) b *)
        symmetry. apply max_l. apply le_S. apply Eb.
    - (* a <= m - 1 *)
      intros b Eb. inversion Eb.
      + replace (Nat.max a (S m)) with (S m). apply le_n.
        (* goal : S m = Nat.max a (S m) *)
        symmetry. apply max_r. apply le_S. apply Ea.
      + subst. apply le_S. apply IHEa. assumption.
  Qed.

  Proposition heap_prop_max : forall t,
      sat_heap_prop t -> max_vertex t = root t.
  Proof.
    intros t E. induction E.
    - (* SatHPSingle *)
      reflexivity.
    - (* SatHPLeft *)
      simpl. apply max_l. rewrite IHE. assumption.
    - (* SatHPRight *)
      simpl. apply max_l. rewrite IHE. assumption.
    - (* SatHPInd *)
      simpl. apply max_l. rewrite IHE1. rewrite IHE2.
      apply max_upper; assumption.
  Qed.

  Definition heap (t:bintree) : Prop :=
    complete t /\ sat_heap_prop t.
  (** A binary tree is called binary heap if and only if it satisfies
      the shape property (completeness) and the heap property. *)

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
