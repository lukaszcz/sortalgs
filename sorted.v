From sortalgs Require Export order.
Require Export Sorting.Permutation.

Import List.ListNotations.
Open Scope list_scope.

Inductive Sorted {A} {dto : DecTotalOrder A} : list A -> Prop :=
| Sorted_0 : Sorted []
| Sorted_1 : forall x, Sorted [x]
| Sorted_2 : forall x y l, Sorted (y :: l) -> leb x y ->
                           Sorted (x :: y :: l).

Lemma lem_sorted_tail {A} {dto : DecTotalOrder A} :
  forall l x, Sorted (x :: l) -> Sorted l.
Proof.
  sauto.
Qed.

(*********************************************************************)

Fixpoint sortedb {A} {dto : DecTotalOrder A} (l : list A) : bool :=
  match l with
  | [] => true
  | [x] => true
  | x :: (y :: l') as t => leb x y && sortedb t
  end.

Lemma lem_sortedb_iff_sorted {A} {dto : DecTotalOrder A} :
  forall l : list A, sortedb l <-> Sorted l.
Proof.
  induction l; sauto brefl: on inv: Sorted.
Qed.

(*********************************************************************)

Definition LeLst {A} {dto : DecTotalOrder A} (x : A) :=
  List.Forall (leb x).

Lemma lem_lelst_nil {A} {dto : DecTotalOrder A} : forall x, LeLst x [].
Proof.
  sauto.
Qed.

Lemma lem_lelst_cons {A} {dto : DecTotalOrder A} :
  forall x y l, LeLst x l -> leb x y -> LeLst x (y :: l).
Proof.
  sauto.
Qed.

Hint Resolve lem_lelst_nil lem_lelst_cons : lelst.

Lemma lem_lelst_trans {A} {dto : DecTotalOrder A} :
  forall l x y, LeLst y l -> leb x y -> LeLst x l.
Proof.
  induction 1; sauto.
Qed.

Lemma lem_lelst_perm {A} {dto : DecTotalOrder A} :
  forall l1 l2 x, Permutation l1 l2 -> LeLst x l1 -> LeLst x l2.
Proof.
  induction 1; sauto lq: on.
Qed.

Lemma lem_lelst_perm_rev {A} {dto : DecTotalOrder A} :
  forall l1 l2 x, Permutation l1 l2 -> LeLst x l2 -> LeLst x l1.
Proof.
  induction 1; sauto lq: on.
Qed.

Lemma lem_lelst_app {A} {dto : DecTotalOrder A} :
  forall l1 l2 x, LeLst x l1 -> LeLst x l2 -> LeLst x (l1 ++ l2).
Proof.
  induction 1; sauto lq: on.
Qed.

Hint Resolve lem_lelst_trans lem_lelst_perm lem_lelst_perm_rev
     lem_lelst_app : lelst.

Lemma lem_lelst_sorted {A} {dto : DecTotalOrder A} :
  forall l x, Sorted (x :: l) <-> LeLst x l /\ Sorted l.
Proof.
  induction l; sauto l: on use: lem_lelst_trans
                     inv: Sorted, List.Forall ctrs: Sorted.
Qed.

(*********************************************************************)

Definition GeLst {A} {dto : DecTotalOrder A} (x : A) (l : list A) :=
  List.Forall (fun y => leb y x) l.

Lemma lem_gelst_nil {A} {dto : DecTotalOrder A} : forall x, GeLst x [].
Proof.
  sauto.
Qed.

Lemma lem_gelst_cons {A} {dto : DecTotalOrder A} :
  forall x y l, GeLst x l -> leb y x -> GeLst x (y :: l).
Proof.
  sauto.
Qed.

Hint Resolve lem_gelst_nil lem_gelst_cons : gelst.

Lemma lem_gelst_trans {A} {dto : DecTotalOrder A} :
  forall l x y, GeLst y l -> leb y x -> GeLst x l.
Proof.
  induction 1; sauto.
Qed.

Lemma lem_gelst_perm {A} {dto : DecTotalOrder A} :
  forall x l1 l2, Permutation l1 l2 -> GeLst x l1 -> GeLst x l2.
Proof.
  induction 1; sauto lq: on.
Qed.

Lemma lem_gelst_perm_rev {A} {dto : DecTotalOrder A} :
  forall l1 l2 x, Permutation l1 l2 -> GeLst x l2 -> GeLst x l1.
Proof.
  induction 1; sauto lq: on.
Qed.

Lemma lem_gelst_app {A} {dto : DecTotalOrder A} :
  forall l1 l2 x, GeLst x l1 -> GeLst x l2 -> GeLst x (l1 ++ l2).
Proof.
  induction 1; sauto lq: on.
Qed.

Hint Resolve lem_gelst_trans lem_gelst_perm lem_gelst_perm_rev
     lem_gelst_app : gelst.
