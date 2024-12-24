Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5145274 : forall s : real -> Prop, ((@FINITE real s) /\ (~ (s = (@EMPTY real)))) -> (@IN real (sup s) s) /\ (forall x : real, (@IN real x s) -> real_le x (sup s)).
