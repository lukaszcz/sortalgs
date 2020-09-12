(******************************************************************)
(* Mergesort (subset types) *)

From sortalgs Require Import sorted.

Open Scope list_scope.
Import List.ListNotations.

Require Import Lia.
Require Import Program.

Lemma lem_sorted_concat_1 {A} {dto : DecTotalOrder A} :
  forall (l l1 l2 : list A) x y,
    Permutation l (l1 ++ y :: l2) -> Sorted (x :: l1) -> leb x y ->
    Sorted (y :: l2) -> Sorted l -> Sorted (x :: l).
Proof.
  intros.
  rewrite lem_lelst_sorted in *.
  sauto db: lelst inv: -.
Qed.

Lemma lem_sorted_concat_2 {A} {dto : DecTotalOrder A} :
  forall (l l1 l2 : list A) x y,
    Permutation l (x :: l1 ++ l2) -> Sorted (x :: l1) -> leb y x ->
    Sorted (y :: l2) -> Sorted l -> Sorted (y :: l).
Proof.
  intros.
  rewrite lem_lelst_sorted in *.
  sauto db: lelst inv: -.
Qed.

Program Fixpoint merge {A} {dto : DecTotalOrder A}
  (l1 l2 : {l | Sorted l}) {measure (List.length l1 + List.length l2)} :
  {l | Sorted l /\ Permutation l (l1 ++ l2)} :=
  match l1 with
  | [] => l2
  | h1 :: t1 =>
    match l2 with
    | [] => l1
    | h2 :: t2 =>
      if leb_total_dec h1 h2 then
        h1 :: merge t1 l2
      else
        h2 :: merge l1 t2
    end
  end.
Next Obligation.
  sauto db: list.
Qed.
Next Obligation.
  eauto using lem_sorted_tail.
Qed.
Next Obligation.
  sauto use: lem_sorted_concat_1.
Qed.
Next Obligation.
  eauto using lem_sorted_tail.
Qed.
Next Obligation.
  simpl; lia.
Qed.
Next Obligation.
  split.
  - sauto use: lem_sorted_concat_2.
  - simpl_sigma.
    rewrite List.app_comm_cons.
    apply Permutation_cons_app.
    intuition.
Qed.

Program Fixpoint split {A} (l : list A) {measure (length l)} :
  { (l1, l2) : list A * list A |
    length l1 + length l2 = length l /\
    length l1 <= length l2 + 1 /\ length l2 <= length l1 + 1 /\
    Permutation l (l1 ++ l2) } :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: t =>
    match split t with
    | (l1, l2) => (x :: l1, y :: l2)
    end
  end.
Solve Obligations with sauto use: Permutation_cons_app.

Lemma lem_split {A} : forall l : list A,
    2 <= List.length l ->
    forall l1 l2, (l1, l2) = ` (split l) ->
    List.length l1 < List.length l /\
    List.length l2 < List.length l.
Proof.
  sauto.
Qed.

Ltac use_lem_split :=
  match goal with
  | [ H1: [] <> ?l, H2: forall x, [x] <> ?l |- _ ] =>
    assert (2 <= length l) by
        (clear - H1 H2; destruct l; hauto depth: 1 inv: list)
  end;
  sauto use: @lem_split.

Obligation Tactic := idtac.

Program Fixpoint mergesort {A} {dto : DecTotalOrder A} (l : list A)
  {measure (List.length l)} : {l' | Sorted l' /\ Permutation l' l} :=
  match l with
  | [] => []
  | [x] => [x]
  | _ =>
    match split l with
    | (l1, l2) => merge (mergesort l1) (mergesort l2)
    end
  end.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  program_simpl; use_lem_split.
Qed.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  program_simpl; use_lem_split.
Qed.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  split.
  - sauto.
  - qauto use: Permutation_app, Permutation_sym, perm_trans.
Qed.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  program_simpl.
Defined.
