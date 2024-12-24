Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3252516 : forall {A : Type'} (P : (A -> Prop) -> Prop), forall a : A, forall t : A -> Prop, (forall s : A -> Prop, (@SUBSET A s (@INSERT A a t)) -> P s) = (forall s : A -> Prop, (@SUBSET A s t) -> (P s) /\ (P (@INSERT A a s))).
