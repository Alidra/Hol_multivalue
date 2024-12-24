Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5293342 : forall s : real -> Prop, forall b : real, forall x : real, ((has_sup s b) /\ (@IN real x s)) -> real_le x b.
