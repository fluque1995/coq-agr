Set Automatic Coercions Import.
Set Implicit Arguments.
Unset Strict Implicit.
From Algebra Require Import Algebra.
From Algebra Require Import Algebra_facts.

Variable R : CRING.
Variable A : ring_algebra R.
Variable x : A.

Definition is_center_element (x : A) : Type :=
  forall y : A, Equal (algebra_mult x y) (algebra_mult y x).


Theorem unit_is_center : is_center_element (ring_algebra_unit A).
Proof.
  intros x.
  refine (@Trans _ (algebra_mult (ring_algebra_unit A) x) x (algebra_mult x (ring_algebra_unit A)) _ _).
  apply ring_algebra_unit_l.
  apply Sym.
  apply ring_algebra_unit_r.
Qed.


Theorem center_A_closed : (forall x y : A, is_center_element x -> is_center_element y -> is_center_element (algebra_mult x y)).
Proof.
  intros x y.
  intros x_center y_center.
  intros z.
  refine (@Trans _ _ (algebra_mult x (algebra_mult y z)) _ _ _).
  exact (ring_algebra_assoc A x y z).
  refine (@Trans _ (algebra_mult x (algebra_mult y z)) (algebra_mult x (algebra_mult z y)) (algebra_mult z (algebra_mult x y)) _ _).
  refine (ALGEBRA_comp _ _).
  exact (@Refl _ x).
  apply y_center.
  refine (@Trans _ (algebra_mult x (algebra_mult z y)) (algebra_mult (algebra_mult x z) y) (algebra_mult z (algebra_mult x y)) _ _).
  apply Sym.
  exact (ring_algebra_assoc A x z y).
  refine (@Trans _ (algebra_mult (algebra_mult x z) y) (algebra_mult (algebra_mult z x) y) (algebra_mult z (algebra_mult x y)) _ _).
  refine (ALGEBRA_comp _ _).
  apply x_center.
  exact (Refl y).
  refine (@Trans _ (algebra_mult (algebra_mult z x) y) (algebra_mult z (algebra_mult x y)) (algebra_mult z (algebra_mult x y)) _ _).
  exact (ring_algebra_assoc A z x y).
  refine (ALGEBRA_comp _ _).
  exact (Refl z).
  refine (ALGEBRA_comp _ _).
  exact (Refl x).
  exact (Refl y).
Qed.


Theorem center_is_comm : (forall x y : A, is_center_element x -> is_center_element y -> Equal (algebra_mult x y) (algebra_mult y x)).
Proof.
  intros x y.
  intros x_center y_center.
  apply x_center.
Qed.


Theorem center_is_submodule : (forall x y : A, is_center_element x -> is_center_element y -> is_center_element (sgroup_law A x y)).
Proof.
  intros x y.
  intros x_center y_center.
  intros z.
  refine (@Trans _ _ (sgroup_law A (algebra_mult x z) (algebra_mult y z)) _ _ _).
  exact (ALGEBRA_lin_left x y z).
  refine (@Trans _ _ (sgroup_law A (algebra_mult z x) (algebra_mult z y)) _ _ _).
  auto with algebra.
  apply Sym.
  exact (ALGEBRA_lin_right z x y).
Qed.
