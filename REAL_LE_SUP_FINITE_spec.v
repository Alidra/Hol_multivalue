Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5147521 : forall s : real -> Prop, forall a : real, ((@FINITE real s) /\ (~ (s = (@EMPTY real)))) -> (real_le a (sup s)) = (exists x : real, (@IN real x s) /\ (real_le a x)).
