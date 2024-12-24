Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5205408 : forall s : real -> Prop, forall t : real -> Prop, (forall a : real, (forall x : real, (@IN real x s) -> real_le a x) = (forall x : real, (@IN real x t) -> real_le a x)) -> (inf s) = (inf t).
