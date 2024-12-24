Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5214027 : forall s : real -> Prop, ((~ (s = (@EMPTY real))) /\ (exists b : real, forall x : real, (@IN real x s) -> real_le b x)) -> (forall x : real, (@IN real x s) -> real_le (inf s) x) /\ (forall b : real, (forall x : real, (@IN real x s) -> real_le b x) -> real_le b (inf s)).
