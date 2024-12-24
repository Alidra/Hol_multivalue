Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3558722 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, ((P (@EMPTY A)) /\ (forall x : A, forall s : A -> Prop, ((P s) /\ ((~ (@IN A x s)) /\ (@FINITE A s))) -> P (@INSERT A x s))) -> forall s : A -> Prop, (@FINITE A s) -> P s.
