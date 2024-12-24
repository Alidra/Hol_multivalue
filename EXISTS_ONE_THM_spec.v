Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem16417 : forall (P : unit -> Prop), (exists x : unit, P x) = (P tt).
