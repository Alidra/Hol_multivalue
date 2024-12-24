Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3184729 : forall {_83123 : Type'}, forall P : (Prop -> _83123 -> Prop) -> Prop, forall x : _83123, (@GSPEC _83123 (fun v : _83123 => P (@SETSPEC _83123 v)) x) = (P (fun p : Prop => fun t : _83123 => p /\ (x = t))).
