Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5252869 : forall (a : real), forall s : real -> Prop, ((@FINITE real s) /\ (~ (s = (@EMPTY real)))) -> ((inf s) = a) = ((@IN real a s) /\ (forall y : real, (@IN real y s) -> real_le a y)).
