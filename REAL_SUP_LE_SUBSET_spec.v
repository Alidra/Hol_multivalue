Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5163728 : forall s : real -> Prop, forall t : real -> Prop, ((~ (s = (@EMPTY real))) /\ ((@SUBSET real s t) /\ (exists b : real, forall x : real, (@IN real x t) -> real_le x b))) -> real_le (sup s) (sup t).
