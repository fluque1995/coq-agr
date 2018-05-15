Require Import Omega.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Fixpoint plus (n m:nat) : nat :=
  match n with
    | O => m
    | S p => S (plus p m)
  end.

Fixpoint mult (n m:nat) : nat :=
  match n with
    | O => O
    | S p => plus m (mult p m)
  end.

Eval compute in mult (S (S (S O))) (S (S O)).


Notation "x + y" := (plus x y) (at level 50, left associativity).
Notation "x * y" := (mult x y) (at level 40, left associativity). 
Eval compute in (S (S (S (S O)))) + (S (S O)).
Eval compute in (S (S (S (S O)))) * (S (S O)).

Lemma plus_0_r:
  forall (n:nat), n = n + O.
Proof.
  intros n.
  induction n as [|n'].
    reflexivity.
    simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Check plus_0_r.

Lemma plus_S_r:
  forall (n m : nat), n + S m = S (n + m).
Proof.
  intros n m.
  induction n as [| n'].
    reflexivity.
    simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_comm:
  forall (n m:nat), n + m = m + n.
Proof.
  intros n m.
  induction n.
    simpl. rewrite <- plus_0_r. reflexivity.
    simpl. rewrite -> IHn. rewrite -> plus_S_r. reflexivity.
Qed.

Lemma plus_assoc:
  forall (n m p: nat), (n + m) + p = n + (m + p).
Proof.
  intros n m p.
  induction p.
  rewrite <- plus_0_r.
  rewrite <- plus_0_r.
  reflexivity.
  rewrite -> (plus_S_r m p).
  rewrite -> (plus_S_r n (m + p)).
  rewrite <- IHp.
  rewrite -> plus_S_r.
  reflexivity.
Qed.

  

Lemma mult_1_r:
  forall (n:nat), n = n * S O.
Proof.
  intros n.
  induction n as [|n'].
  reflexivity.
  simpl. rewrite <- IHn'. reflexivity.
Qed.

Lemma mult_O_r:
  forall (n:nat), n * O = O.
Proof.
  intros n.
  induction n as [|n'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Lemma mult_S_r:
  forall (n m:nat), n * S m = n * m + n.
Proof.
  intros n m.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite -> IHn.
  rewrite <- plus_S_r.
  rewrite <- (plus_S_r (n * m) n).
  rewrite <- plus_assoc.
  reflexivity.
Qed.
  
        
Theorem mult_comm:
  forall (n m : nat), n * m = m * n.
Proof.
  intros n m.
  induction n.
  simpl.
  rewrite -> mult_O_r.
  reflexivity.
  simpl.
  rewrite mult_S_r.
  rewrite -> IHn.
  rewrite -> plus_comm.
  reflexivity.
Qed.
