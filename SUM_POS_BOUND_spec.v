Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7109270 : forall {A : Type'}, forall f : A -> real, forall b : real, forall s : A -> Prop, ((@FINITE A s) /\ ((forall x : A, (@IN A x s) -> real_le (real_of_num (NUMERAL 0)) (f x)) /\ (real_le (@sum A s f) b))) -> forall x : A, (@IN A x s) -> real_le (f x) b.
