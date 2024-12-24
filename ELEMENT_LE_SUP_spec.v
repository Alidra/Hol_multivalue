Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5199214 : forall s : real -> Prop, forall a : real, ((exists b : real, forall x : real, (@IN real x s) -> real_le x b) /\ (@IN real a s)) -> real_le a (sup s).
