Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3184739 : forall {_83095 : Type'}, (forall p : _83095 -> Prop, forall x : _83095, (@IN _83095 x (@GSPEC _83095 (fun v : _83095 => exists y : _83095, @SETSPEC _83095 v (p y) y))) = (p x)) = (forall p : _83095 -> Prop, forall x : _83095, (@IN _83095 x (@GSPEC _83095 (fun v : _83095 => exists y : _83095, @SETSPEC _83095 v (p y) y))) = (p x)).
