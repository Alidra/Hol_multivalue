Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3184746 : forall {_83064 : Type'} (P : (Prop -> _83064 -> Prop) -> Prop), forall x : _83064, (@IN _83064 x (@GSPEC _83064 (fun v : _83064 => P (@SETSPEC _83064 v)))) = (P (fun p : Prop => fun t : _83064 => p /\ (x = t))).
