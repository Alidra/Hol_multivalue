Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5292278 : forall s : real -> Prop, forall b : real, forall x : real, ((has_inf s b) /\ (@IN real x s)) -> real_le b x.
