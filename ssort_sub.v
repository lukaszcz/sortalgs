(* Selection sort (subset types) *)

From sortalgs Require Import sorted.

Require List.
Import ListNotations.

Require Import Program.

Ltac solve_select :=
  destruct_sigma;
  simp_hyps;
  split; [
    match goal with
    | [ H : Permutation _ _ |- _ ] =>
      clear -H; hauto ctrs: Permutation
    end
  | match goal with
    | [H : Permutation (?x :: ?t) (?x1 :: ?x2) |- _ ] =>
      assert (leb x1 x);
        [ let H0 := fresh "H" in
          assert (H0: LeLst x1 (x1 :: x2)) by sauto use: (leb_refl x1);
          assert (LeLst x1 (x :: t));
          [ clear -H0 H; hauto db: lelst | sauto ] | sauto ]
    end ].

Program Fixpoint select {A} `{DecTotalOrder A} (x : A) (l : list A)
        {measure (length l)}
  : { (y, l') : A * list A |
      Permutation (x :: l) (y :: l') /\ LeLst y l' /\
      length l' = length l } :=
  match l with
  | h :: t =>
    if leb_total_dec x h then
      match select x t with
      | (y, l2) => (y, h :: l2)
      end
    else
      match select h t with
      | (y, l2) => (y, x :: l2)
      end
  | [] =>
    (x, [])
  end.
Next Obligation.
  solve_select.
Qed.
Next Obligation.
  solve_select.
Qed.
Next Obligation.
  sauto.
Qed.

Program Fixpoint ssort {A} `{DecTotalOrder A} (l : list A) {measure (length l)}
  : { l' : list A | Sorted l' /\ Permutation l' l } :=
  match l with
  | h :: t =>
    match select h t with
    | (x, l2) => x :: ssort l2
    end
  | [] => []
  end.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  destruct_sigma.
  simp_hyps.
  split.
  - rewrite lem_lelst_sorted.
    qauto use: Permutation_sym db: lelst.
  - hauto use: Permutation_sym, Permutation_cons, perm_trans.
Qed.
Next Obligation.
  sauto.
Qed.
