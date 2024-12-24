Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem16018 : forall P : unit -> Prop, (P tt) -> forall x : unit, P x.
