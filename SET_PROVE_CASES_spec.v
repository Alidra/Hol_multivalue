Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3450827 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, ((P (@EMPTY A)) /\ (forall a : A, forall s : A -> Prop, (~ (@IN A a s)) -> P (@INSERT A a s))) -> forall s : A -> Prop, P s.
