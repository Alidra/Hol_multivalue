Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7929851 : forall {A : Type'}, forall P : (tybit1 A) -> Prop, (forall a : finite_sum (finite_sum A A) unit, P (@_103802 A a)) -> forall x : tybit1 A, P x.
