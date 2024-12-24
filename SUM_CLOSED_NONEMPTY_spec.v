Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7205598 : forall {A : Type'}, forall P : real -> Prop, forall f : A -> real, forall s : A -> Prop, ((@FINITE A s) /\ ((~ (s = (@EMPTY A))) /\ ((forall x : real, forall y : real, ((P x) /\ (P y)) -> P (real_add x y)) /\ (forall a : A, (@IN A a s) -> P (f a))))) -> P (@sum A s f).
