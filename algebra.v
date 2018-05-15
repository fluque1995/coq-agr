Set Automatic Coercions Import.
Set Implicit Arguments.
Unset Strict Implicit.
Add LoadPath "/home/ritaso/.opam/system/bin".
From Algebra Require Import Algebra.
From Algebra Require Import Field_cat.
From Coq.Setoids Require Import Setoid.
From Algebra Require Import Algebra_facts.

Variable R : CRING.
Variable A : ring_algebra R.
Variable x : A.

Definition is_center_element (x : A) : Type :=
  forall y : A, Equal (algebra_mult x y) (algebra_mult y x).

Theorem centre_A_closed : (forall x y : A, is_center_element x -> is_center_element y -> is_center_element (algebra_mult x y)).
Proof.
  intros x y.
  intros x_center y_center.
  intros z.
  apply RING_ALGEBRA_assoc.
  refine (Trans _ _).
    exact ring_algebra_assoc.
  (*
  replace (algebra_mult (algebra_mult x y) z) with (algebra_mult x (algebra_mult y z)).
  replace (algebra_mult x (algebra_mult y z)) with (algebra_mult x (algebra_mult z y)).
  replace (algebra_mult x (algebra_mult z y)) with (algebra_mult (algebra_mult x z) y).
  replace (algebra_mult (algebra_mult x z) y) with (algebra_mult (algebra_mult z x) y).
  replace (algebra_mult (algebra_mult z x) y) with (algebra_mult z (algebra_mult x y)).
  apply Refl.
  
  unfold algebra_mult in |- *.
  refine (@Leibnitz_set_prop _ x_is_leibnitz y_is_leibnitz _).
    apply Sym.
    refine (@RING_ALGEBRA_assoc _ _ _ _ _).
   *)
