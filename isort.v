(******************************************************************)
(* Insertion sort *)

From sortalgs Require Import sorted.

Import List.ListNotations.
Open Scope list_scope.

(* insert a number into a sorted list preserving the sortedness *)
Fixpoint insert {A} {dto : DecTotalOrder A} (l : list A) (x : A) : list A :=
  match l with
  | [] => [x]
  | h :: t => if leb_total_dec x h then x :: l else h :: insert t x
  end.

(* insertion sort *)
Fixpoint isort {A} {dto : DecTotalOrder A} (l : list A) : list A :=
  match l with
  | [] => []
  | h :: t => insert (isort t) h
  end.

Lemma lem_insert_sorted_hlp {A} {dto : DecTotalOrder A} :
  forall (l : list A) x y,
    leb x y -> Sorted (x :: l) -> Sorted (x :: insert l y).
Proof.
  induction l; sauto.
Qed.

Lemma lem_insert_sorted {A} {dto : DecTotalOrder A} (l : list A) (x : A) :
  Sorted l -> Sorted (insert l x).
Proof.
  destruct l; qauto use: lem_insert_sorted_hlp ctrs: Sorted.
Qed.

Lemma lem_isort_sorted {A} {dto : DecTotalOrder A} :
  forall l : list A, Sorted (isort l).
Proof.
  induction l; sauto use: lem_insert_sorted.
Qed.

Lemma lem_insert_perm {A} {dto : DecTotalOrder A} :
  forall (l : list A) x, Permutation (insert l x) (x :: l).
Proof.
  induction l; sauto.
Qed.

Lemma lem_isort_perm {A} {dto : DecTotalOrder A} :
  forall l : list A, Permutation (isort l) l.
Proof.
  induction l; sauto use: lem_insert_perm.
Qed.
