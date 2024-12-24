Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5140310 : forall s : real -> Prop, ((@FINITE real s) /\ (~ (s = (@EMPTY real)))) -> exists b : real, (@IN real b s) /\ (forall x : real, (@IN real x s) -> real_le x b).
