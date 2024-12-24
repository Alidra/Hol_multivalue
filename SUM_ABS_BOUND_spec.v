Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7137133 : forall {A : Type'}, forall s : A -> Prop, forall f : A -> real, forall b : real, ((@FINITE A s) /\ (forall x : A, (@IN A x s) -> real_le (real_abs (f x)) b)) -> real_le (real_abs (@sum A s f)) (real_mul (real_of_num (@CARD A s)) b).
