Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5241000 : forall s : real -> Prop, forall t : real -> Prop, ((~ (t = (@EMPTY real))) /\ ((@SUBSET real t s) /\ (exists b : real, forall x : real, (@IN real x s) -> real_le b x))) -> real_le (inf s) (inf t).
