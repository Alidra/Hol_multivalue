Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3184692 : forall {_83123 : Type'} (P : (Prop -> _83123 -> Prop) -> Prop) (x : _83123), (P (@SETSPEC _83123 x)) = (P (fun p : Prop => fun t : _83123 => p /\ (x = t))).
