Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5308185 : forall s : real -> Prop, forall l : real, forall c : real, ((has_inf s l) /\ (real_lt l c)) -> exists x : real, (@IN real x s) /\ (real_lt x c).
