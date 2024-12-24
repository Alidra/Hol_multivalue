Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5282345 : forall s : real -> Prop, forall t : real -> Prop, ((~ (s = (@EMPTY real))) /\ ((~ (t = (@EMPTY real))) /\ ((exists b : real, forall x : real, (@IN real x s) -> real_le b x) /\ (exists c : real, forall x : real, (@IN real x t) -> real_le c x)))) -> (inf (@UNION real s t)) = (real_min (inf s) (inf t)).
