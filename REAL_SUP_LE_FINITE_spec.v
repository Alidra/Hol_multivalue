Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5149774 : forall s : real -> Prop, forall a : real, ((@FINITE real s) /\ (~ (s = (@EMPTY real)))) -> (real_le (sup s) a) = (forall x : real, (@IN real x s) -> real_le x a).
