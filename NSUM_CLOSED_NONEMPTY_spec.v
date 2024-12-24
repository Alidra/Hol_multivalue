Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7036602 : forall {A : Type'}, forall P : nat -> Prop, forall f : A -> nat, forall s : A -> Prop, ((@FINITE A s) /\ ((~ (s = (@EMPTY A))) /\ ((forall x : nat, forall y : nat, ((P x) /\ (P y)) -> P (Nat.add x y)) /\ (forall a : A, (@IN A a s) -> P (f a))))) -> P (@nsum A s f).
