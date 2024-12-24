Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7030906 : forall {A : Type'}, forall P : nat -> Prop, forall f : A -> nat, forall s : A -> Prop, ((P (NUMERAL 0)) /\ ((forall x : nat, forall y : nat, ((P x) /\ (P y)) -> P (Nat.add x y)) /\ (forall a : A, (@IN A a s) -> P (f a)))) -> P (@nsum A s f).
