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

Lemma lem_lelst_sorted {A} {dto : DecTotalOrder A} :
  forall l x, Sorted (x :: l) <-> LeLst x l /\ Sorted l.
Proof.
  induction l; sauto l: on use: lem_lelst_trans
                     inv: Sorted, List.Forall ctrs: Sorted.
Qed.

Lemma lem_lelst_perm {A} {dto : DecTotalOrder A} :
  forall l1 l2 x, Permutation l1 l2 -> LeLst x l1 -> LeLst x l2.
Proof.
  induction 1; sauto.
Qed.

Lemma lem_lelst_perm_rev {A} {dto : DecTotalOrder A} :
  forall l1 l2 x, Permutation l1 l2 -> LeLst x l2 -> LeLst x l1.
Proof.
  induction 1; sauto.
Qed.

Lemma lem_lelst_app {A} {dto : DecTotalOrder A} :
  forall l1 l2 x, LeLst x l1 -> LeLst x l2 -> LeLst x (l1 ++ l2).
Proof.
  induction 1; sauto.
Qed.

Hint Resolve lem_lelst_trans lem_lelst_perm lem_lelst_perm_rev
     lem_lelst_app : lelst.
