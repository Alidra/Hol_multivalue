Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3183558 : forall {_83123 : Type'} (x : _83123), forall x' : Prop, forall x'' : _83123, (@SETSPEC _83123 x x' x'') = (x' /\ (x = x'')).