(********************************************************************************)
(* Quicksort (subset types) *)

From sortalgs Require Import sorted.

Open Scope list_scope.
Import List.ListNotations.

Require Import Program.

Lemma lem_partition `{DecTotalOrder} :
  forall x l1 l2, Sorted l1 -> Sorted l2 -> GeLst x l1 -> LeLst x l2 ->
                  Sorted (l1 ++ x :: l2).
Proof.
  induction l1.
  - inversion 4; sauto lq: on.
  - inversion 1; inversion 2; hauto use: lem_sorted_tail ctrs: Sorted.
Qed.

Program Fixpoint partition {A} `{DecTotalOrder A} (x : A) (l : list A)
  {measure (length l)} :
  { (l1, l2) : list A * list A |
    GeLst x l1 /\ LeLst x l2 /\ Permutation l (l1 ++ l2) } :=
  match l with
  | [] => ([], [])
  | h :: t =>
    match partition x t with
    | (t1, t2) =>
      if leb_total_dec h x then
        (h :: t1, t2)
      else
        (t1, h :: t2)
    end
  end.
Solve Obligations with sauto use: Permutation_middle.

Program Fixpoint qsort {A} `{DecTotalOrder A} (l : list A) {measure (length l)}
  : {l' | Sorted l' /\ Permutation l l'} :=
  match l with
  | [] => []
  | h :: t =>
    match partition h t with
    | (t1, t2) => qsort t1 ++ [h] ++ qsort t2
    end
  end.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  hauto use: Permutation_length db: list.
Qed.
Next Obligation.
  hauto use: Permutation_length db: list.
Qed.
Next Obligation.
  destruct_sigma; simp_hyps; split.
  - eauto using lem_gelst_perm, lem_lelst_perm, lem_partition.
  - eauto using perm_trans, perm_skip, Permutation_middle, Permutation_app.
Qed.
