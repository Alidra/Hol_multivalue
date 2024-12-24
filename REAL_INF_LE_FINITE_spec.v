Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5227045 : forall s : real -> Prop, forall a : real, ((@FINITE real s) /\ (~ (s = (@EMPTY real)))) -> (real_le (inf s) a) = (exists x : real, (@IN real x s) /\ (real_le x a)).
