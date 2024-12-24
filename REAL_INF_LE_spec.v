Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5269266 : forall s : real -> Prop, forall a : real, forall b : real, forall y : real, ((@IN real y s) /\ ((real_le y b) /\ (forall x : real, (@IN real x s) -> real_le a x))) -> real_le (inf s) b.
