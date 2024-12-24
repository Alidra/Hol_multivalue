Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5238253 : forall (s : real -> Prop), forall b : real, ((~ (s = (@EMPTY real))) /\ (forall x : real, (@IN real x s) -> real_le b x)) -> real_le b (inf s).
