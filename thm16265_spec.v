Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem16265 : forall (P : unit -> Prop), (((forall x : unit, P x) -> P tt) /\ ((P tt) -> forall x : unit, P x)) = ((forall x : unit, P x) = (P tt)).
