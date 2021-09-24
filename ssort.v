(* Selection sort *)

From sortalgs Require Import sorted.

Require List.
Import ListNotations.

Require Import Recdef.

Fixpoint select {A} `{DecTotalOrder A} (x : A) (l : list A) : A * list A :=
  match l with
  | h :: t =>
    if leb x h then
      let (y, l2) := select x t in
      (y, h :: l2)
    else
      let (y, l2) := select h t in
      (y, x :: l2)
  | [] =>
    (x, [])
  end.

Lemma lem_select_length `{DecTotalOrder} :
  forall l l' x y, select x l = (y, l') -> length l' = length l.
Proof.
  induction l; hauto.
Qed.

Lemma lem_select_perm `{DecTotalOrder} :
  forall l l' x y, select x l = (y, l') -> Permutation (x :: l) (y :: l').
Proof.
  induction l; hauto q: on inv: Permutation ctrs: Permutation.
Qed.

Lemma lem_select_leb `{DecTotalOrder} :
  forall l l' x y, select x l = (y, l') -> leb y x.
Proof.
  induction l; [ sauto | sauto use: lem_neg_leb ].
Qed.

Lemma lem_select_lelst `{DecTotalOrder} :
  forall l l' x y, select x l = (y, l') -> LeLst y l'.
Proof.
  induction l; sauto use: lem_select_leb, lem_neg_leb.
Qed.

Function ssort {A} {dto: DecTotalOrder A} (l : list A) {measure length l}
  : list A :=
  match l with
  | h :: t =>
    let (x, l2) := select h t in
    x :: ssort l2
  | [] => []
  end.
Proof.
  intros; sauto lq: on use: lem_select_length.
  (* Without explicit "intros" lem_select_length would be added to
     the context first, with introductions done afterwards. This
     confuses sauto in this particular case. *)
Defined.

Arguments ssort {_ _}.

Lemma lem_ssort_perm `{DecTotalOrder} :
  forall l, Permutation (ssort l) l.
Proof.
  intro l.
  functional induction (ssort l).
  - hauto use: lem_select_perm, Permutation_sym, Permutation_cons, perm_trans.
  - sauto.
Qed.

Lemma lem_ssort_sorted `{DecTotalOrder} :
  forall l, Sorted (ssort l).
Proof.
  intro l.
  functional induction (ssort l).
  - rewrite lem_lelst_sorted.
    hauto use: lem_select_lelst, lem_ssort_perm.
  - sauto.
Qed.
