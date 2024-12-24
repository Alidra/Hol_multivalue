Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3211641 : forall {_83095 : Type'} (p : _83095 -> Prop) (x : _83095), ((fun x' : _83095 => (@IN _83095 x' (@GSPEC _83095 (fun v : _83095 => exists y : _83095, @SETSPEC _83095 v (p y) y))) = (p x')) x) = ((@IN _83095 x (@GSPEC _83095 (fun v : _83095 => exists y : _83095, @SETSPEC _83095 v (p y) y))) = (p x)).
