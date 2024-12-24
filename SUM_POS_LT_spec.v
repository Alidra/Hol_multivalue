Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7078795 : forall {A : Type'}, forall f : A -> real, forall s : A -> Prop, ((@FINITE A s) /\ ((forall x : A, (@IN A x s) -> real_le (real_of_num (NUMERAL 0)) (f x)) /\ (exists x : A, (@IN A x s) /\ (real_lt (real_of_num (NUMERAL 0)) (f x))))) -> real_lt (real_of_num (NUMERAL 0)) (@sum A s f).
