(******************************************************************)
(* Insertion sort *)

From sortalgs Require Import sorted.

Import List.ListNotations.
Open Scope list_scope.

(* insert a number into a sorted list preserving the sortedness *)
Fixpoint insert {A} `{DecTotalOrder A} (l : list A) (x : A) : list A :=
  match l with
  | [] => [x]
  | h :: t => if leb_total_dec x h then x :: l else h :: insert t x
  end.

(* insertion sort *)
Fixpoint isort {A} `{DecTotalOrder A} (l : list A) : list A :=
  match l with
  | [] => []
  | h :: t => insert (isort t) h
  end.

Lemma lem_insert_sorted_hlp `{DecTotalOrder} :
  forall l x y,
    leb x y -> Sorted (x :: l) -> Sorted (x :: insert l y).
Proof.
  induction l; sauto q: on inv: Sorted ctrs: Sorted.
Qed.

Lemma lem_insert_sorted `{DecTotalOrder} :
  forall l x, Sorted l -> Sorted (insert l x).
Proof.
  destruct l; qauto use: lem_insert_sorted_hlp ctrs: Sorted.
Qed.

Lemma lem_isort_sorted `{DecTotalOrder} :
  forall l, Sorted (isort l).
Proof.
  induction l; sauto use: lem_insert_sorted.
Qed.

Lemma lem_insert_perm `{DecTotalOrder} :
  forall l x, Permutation (insert l x) (x :: l).
Proof.
  induction l; sauto.
Qed.

Lemma lem_isort_perm `{DecTotalOrder} :
  forall l, Permutation (isort l) l.
Proof.
  induction l; sauto use: lem_insert_perm.
Qed.

(* Boolean version *)

Lemma lem_insert_sortedb_hlp `{DecTotalOrder} :
  forall l x y,
    leb x y -> sortedb (x :: l) -> sortedb (x :: insert l y).
Proof.
  induction l; hauto brefl: on.
Qed.

Lemma lem_insert_sortedb `{DecTotalOrder} :
  forall l x, sortedb l -> sortedb (insert l x).
Proof.
  destruct l; hauto brefl: on use: lem_insert_sortedb_hlp.
Qed.

Lemma lem_isort_sortedb `{DecTotalOrder} :
  forall l, sortedb (isort l).
Proof.
  induction l; sauto use: lem_insert_sortedb.
Qed.
