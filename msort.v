(******************************************************************)
(* Mergesort *)

From sortalgs Require Import sorted.

Open Scope list_scope.
Import List.ListNotations.

Require Import Recdef.

Definition length_sum {A} (p : list A * list A) :=
  match p with
  | (l1, l2) => List.length l1 + List.length l2
  end.

Function merge {A} {dto : DecTotalOrder A}
  (p : list A * list A) {measure length_sum p} : list A :=
  match fst p with
  | [] => snd p
  | h1 :: t1 =>
    match snd p with
    | [] => h1 :: t1
    | h2 :: t2 =>
      if leb h1 h2 then
        h1 :: merge (t1, snd p)
      else
        h2 :: merge (fst p, t2)
    end
  end.
Proof.
  all: sauto.
Defined.

Arguments merge {_ _}.

Function split {A} (l : list A) : list A * list A :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: t =>
    match split t with
    | (l1, l2) => (x :: l1, y :: l2)
    end
  end.

Lemma lem_split_sum {A} : forall l : list A,
    forall l1 l2, split l = (l1, l2) ->
                  length l = length l1 + length l2.
Proof.
  intro l.
  functional induction (split l); sauto.
Qed.

Lemma lem_split {A} : forall l : list A,
    2 <= List.length l ->
    forall l1 l2, split l = (l1, l2) ->
    List.length l1 < List.length l /\
    List.length l2 < List.length l.
Proof.
  intros [|x [|y l]]; hauto use: @lem_split_sum.
Qed.

Function msort {A} {dto : DecTotalOrder A} (l : list A)
  {measure List.length l} : list A :=
  match l with
  | [] => []
  | [x] => [x]
  | _ =>
    match split l with
    | (l1, l2) => merge (msort l1, msort l2)
    end
  end.
Proof.
  all:
    intros; assert (Hlen: 2 <= length l) by sauto;
    hauto use: (lem_split l Hlen).
Defined.

Arguments msort {_ _}.

Lemma lem_merge_perm {A} {dto : DecTotalOrder A} :
  forall l1 l2, Permutation (merge (l1, l2)) (l1 ++ l2).
Proof.
  enough (forall p, Permutation (merge p) (fst p ++ snd p)) by sauto.
  intro p.
  functional induction (merge p) as [ | | | ? ? ? ? ? ? E].
  - sauto.
  - sauto db: list.
  - sauto db: list.
  - rewrite E; hauto use: Permutation_middle.
Qed.

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

Lemma lem_merge_sorted {A} {dto : DecTotalOrder A} :
  forall l1 l2, Sorted l1 -> Sorted l2 -> Sorted (merge (l1, l2)).
Proof.
  enough (forall p, Sorted (fst p) -> Sorted (snd p) -> Sorted (merge p)) by sauto.
  intro p.
  functional induction (merge p) as [ | | ? h1 t1 E1 h2 t2 E2 |
                                      ? h1 t1 E1 h2 t2 E2 ].
  - sauto.
  - sauto.
  - simpl in *.
    intros.
    rewrite E1 in *.
    rewrite E2 in *.
    assert (Sorted (merge (t1, h2 :: t2))).
    { qauto use: lem_sorted_tail. }
    hauto use: lem_sorted_concat_1, lem_merge_perm.
  - simpl in *.
    intros.
    rewrite E1 in *.
    rewrite E2 in *.
    assert (Sorted (merge (h1 :: t1, t2))).
    { qauto use: lem_sorted_tail. }
    eapply lem_sorted_concat_2; hauto use: leb_total, lem_merge_perm.
Qed.

Lemma lem_split_perm {A} :
  forall l l1 l2 : list A, split l = (l1, l2) -> Permutation l (l1 ++ l2).
Proof.
  intro l.
  functional induction (split l).
  - hauto.
  - hauto.
  - hauto use: perm_skip, Permutation_cons_app.
Qed.

Lemma lem_msort_perm {A} {dto : DecTotalOrder A} :
  forall l, Permutation (msort l) l.
Proof.
  intro l.
  functional induction (msort l) as [ | | ? ? ? ? l1 l2 ].
  - sauto.
  - sauto.
  - assert (HH1: Permutation (l1 ++ l2) l).
    { hauto use: (lem_split_perm l l1 l2), Permutation_sym. }
    assert (Permutation (merge (msort l1, msort l2)) (msort l1 ++ msort l2)).
    { hauto use: (lem_merge_perm (msort l1) (msort l2)). }
    assert (Permutation (msort l1 ++ msort l2) (l1 ++ l2)).
    { hauto use: Permutation_app. }
    assert (HH2: Permutation (merge (msort l1, msort l2)) (l1 ++ l2)).
    { eapply perm_trans; eassumption. }
    eapply perm_trans; eassumption.
Qed.

Lemma lem_msort_sorted {A} {dto : DecTotalOrder A} :
  forall l, Sorted (msort l).
Proof.
  intro l.
  functional induction (msort l).
  - hauto.
  - hauto.
  - hauto use: lem_merge_sorted.
Qed.
