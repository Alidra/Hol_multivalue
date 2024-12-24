Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5222545 : forall s : real -> Prop, ((@FINITE real s) /\ (~ (s = (@EMPTY real)))) -> (@IN real (inf s) s) /\ (forall x : real, (@IN real x s) -> real_le (inf s) x).
