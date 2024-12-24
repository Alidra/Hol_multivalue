Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3183343 : forall {_83064 : Type'} (x : _83064), (forall x' : Prop, forall x'' : _83064, (@SETSPEC _83064 x x' x'') = (x' /\ (x = x''))) = ((@SETSPEC _83064 x) = (fun p : Prop => fun t : _83064 => p /\ (x = t))).
