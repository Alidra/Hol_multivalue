Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5204233 : forall s : real -> Prop, (inf s) = (@ε real (fun a : real => (forall x : real, (@IN real x s) -> real_le a x) /\ (forall b : real, (forall x : real, (@IN real x s) -> real_le b x) -> real_le b a))).
