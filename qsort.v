(********************************************************************************)
(* Quicksort *)

From sortalgs Require Import sorted.

Open Scope list_scope.
Import List.ListNotations.

Require Import Recdef.

Lemma lem_partition `{DecTotalOrder} :
  forall x l1 l2, Sorted l1 -> Sorted l2 -> GeLst x l1 -> LeLst x l2 ->
                        Sorted (l1 ++ x :: l2).
Proof.
  induction l1.
  - inversion 4; sauto lq: on.
  - inversion 1; inversion 2; hauto use: lem_sorted_tail ctrs: Sorted.
Qed.

Function partition {A} {dto : DecTotalOrder A} (x : A) (l : list A)
  {measure length l} : list A * list A :=
  match l with
  | [] => ([], [])
  | h :: t =>
    match partition x t with
    | (t1, t2) =>
      if leb h x then
        (h :: t1, t2)
      else
        (t1, h :: t2)
    end
  end.
Proof.
  sauto.
Defined.

Arguments partition {_ _}.

Lemma lem_partition_perm `{DecTotalOrder} :
  forall l l1 l2 x, partition x l = (l1, l2) -> Permutation l (l1 ++ l2).
Proof.
  induction l.
  - sauto.
  - intros *.
    rewrite partition_equation.
    hauto use: Permutation_middle, @leb_total.
Qed.

Lemma lem_partition_parted `{DecTotalOrder} :
  forall l l1 l2 x, partition x l = (l1, l2) -> GeLst x l1 /\ LeLst x l2.
Proof.
  induction l.
  - sauto.
  - intros *.
    rewrite partition_equation.
    hauto use: lem_neg_leb.
Qed.

Function qsort {A} {dto : DecTotalOrder A} (l : list A) {measure length l}
  : list A :=
  match l with
  | [] => []
  | h :: t =>
    match partition h t with
    | (t1, t2) => qsort t1 ++ [h] ++ qsort t2
    end
  end.
Proof.
  all: intros; hauto use: lem_partition_perm, Permutation_length db: list.
Defined.

Arguments qsort {_ _}.

Lemma lem_qsort_perm `{DecTotalOrder} :
  forall l, Permutation l (qsort l).
Proof.
  intro l.
  functional induction (qsort l).
  - sauto.
  - hauto lq: on use: lem_partition_perm, perm_trans, perm_skip, Permutation_middle, Permutation_app.
Qed.

Lemma lem_qsort_sorted `{DecTotalOrder} :
  forall l, Sorted (qsort l).
Proof.
  intro l.
  functional induction (qsort l).
  - sauto.
  - hauto lq: on use: lem_partition_parted, lem_qsort_perm, lem_gelst_perm, lem_lelst_perm, lem_partition.
Qed.
