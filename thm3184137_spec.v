Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3184137 : forall {_83095 : Type'} (p : _83095 -> Prop) (x : _83095), (exists y : _83095, (p y) /\ (x = y)) = (p x).