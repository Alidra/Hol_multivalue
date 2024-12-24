Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5311014 : forall s : real -> Prop, forall l : real, forall c : real, ((has_sup s l) /\ (real_lt c l)) -> exists x : real, (@IN real x s) /\ (real_lt c x).
