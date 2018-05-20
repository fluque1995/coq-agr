
Theorem tautology : (forall A : Prop, A -> A).
Proof.
  intros A.
  intros proof_of_A.
  exact proof_of_A.
Qed.

Theorem proof_by_cases : (forall A B C : Prop, (A -> C) /\ (B -> C) /\ (A \/ B) -> C).
Proof.
  intros A B C.
  intros hypotheses.
  destruct hypotheses as [a_implies_c right].
  destruct right as [b_implies_c a_or_b].
  case a_or_b.
    (* suppose a_or_b is (or_introl a) *)
    intros proof_of_a.
    refine (a_implies_c _).
      exact proof_of_a.
    (* suppose a_or_b is (or_intror b) *)
    intros proof_of_b.
    refine (b_implies_c _).
      exact proof_of_b.
Qed.

Theorem syllogism : (forall A B C : Prop, (A -> B) -> (B -> C) -> (A -> C)).
Proof.
  intros A B C.
  intros a_implies_b.
  intros b_implies_c.
  intros proof_of_a.
  refine (b_implies_c _).
    refine (a_implies_b _).
      exact proof_of_a.
Qed.

Theorem triple_implies_simple : (forall A : Prop, ~(~(~A)) -> ~A).
Proof.
  intros A.
  intros not_not_not_a.
  intros proof_of_a.
  refine (not_not_not_a _).
  intros not_a.
  refine (not_a _).
  exact proof_of_a.
Qed.
