Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5301261 : forall s : real -> Prop, (exists l : real, has_inf s l) = ((~ (s = (@EMPTY real))) /\ (exists b : real, forall x : real, (@IN real x s) -> real_le b x)).
