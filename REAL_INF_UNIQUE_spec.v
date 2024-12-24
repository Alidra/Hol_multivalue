Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5236201 : forall s : real -> Prop, forall b : real, ((forall x : real, (@IN real x s) -> real_le b x) /\ (forall b' : real, (real_lt b b') -> exists x : real, (@IN real x s) /\ (real_lt x b'))) -> (inf s) = b.
