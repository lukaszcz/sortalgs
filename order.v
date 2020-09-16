From Hammer Require Export Tactics Reflect.
Require Import Recdef.

Require Export List.
Import List.ListNotations.
Open Scope list_scope.

Class DecTotalOrder (A : Type) := {
  leb : A -> A -> bool;
  leb_total : forall x y, leb x y \/ leb y x;
  leb_antisym : forall x y, leb x y -> leb y x -> x = y;
  leb_trans : forall x y z, leb x y -> leb y z -> leb x z }.

Arguments leb {A _}.
Arguments leb_total {A _}.
Arguments leb_antisym {A _}.
Arguments leb_trans {A _}.

Lemma leb_refl {A} {dto : DecTotalOrder A} : forall x, leb x x.
Proof.
  intro x; destruct (leb_total x x); auto.
Qed.

Lemma lem_neg_leb {A} {dto : DecTotalOrder A} :
  forall x y, ~ (leb x y) -> leb y x.
Proof.
  qauto use: @leb_total.
Qed.

Definition leb_total_dec {A} {dto : DecTotalOrder A}
  : forall x y, {leb x y}+{leb y x}.
  intros x y.
  sdestruct (leb x y).
  - left; constructor.
  - right; destruct (leb_total x y); auto.
Defined.

Definition eq_dec {A} {dto : DecTotalOrder A} : forall x y : A, {x = y}+{x <> y}.
  intros x y.
  sdestruct (leb x y).
  - sdestruct (leb y x).
    + auto using leb_antisym.
    + sauto.
  - sdestruct (leb y x).
    + sauto.
    + destruct (leb_total_dec x y); auto.
Defined.

Definition eqb {A} {dto : DecTotalOrder A} (x y : A) : bool :=
  if eq_dec x y then
    true
  else
    false.

Definition ltb {A} {dto : DecTotalOrder A} (x y : A) : bool :=
  leb x y && negb (eqb x y).

Definition leb_ltb_dec {A} {dto : DecTotalOrder A} (x y : A) : {leb x y}+{ltb y x}.
  destruct (leb_total_dec x y).
  - left; sauto.
  - unfold ltb, negb, eqb.
    destruct (eq_dec y x).
    + left; sauto.
    + right; sauto brefl: on.
Defined.

Lemma lem_ltb_leb_incl {A} {dto : DecTotalOrder A} :
  forall x y : A, ltb x y -> leb x y.
Proof.
  sauto brefl: on unfold: ltb.
Qed.

Function lexb {A} {dto : DecTotalOrder A} (l1 l2 : list A) : bool :=
  match l1 with
  | [] => true
  | x :: l1' =>
    match l2 with
    | [] => false
    | y :: l2' =>
      if eq_dec x y then
        lexb l1' l2'
      else
        leb x y
    end
  end.

Instance dto_list {A} {dto_a : DecTotalOrder A} : DecTotalOrder (list A).
Proof.
  apply Build_DecTotalOrder with (leb := lexb).
  - induction x; sauto.
  - intros x y.
    functional induction (lexb x y).
    + sauto inv: list.
    + sauto.
    + sauto.
    + sauto inv: - use: leb_antisym.
  - intros x y.
    functional induction (lexb x y); sauto.
Defined.

Instance dto_nat : DecTotalOrder nat.
Proof.
  apply Build_DecTotalOrder with (leb := Nat.leb);
    induction x; sauto.
Defined.
