Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3184719 : forall {_83152 _83169 : Type'}, (forall p : _83152 -> Prop, forall x : _83152, (@GSPEC _83152 (fun v : _83152 => exists y : _83152, @SETSPEC _83152 v (p y) y) x) = (p x)) /\ (forall p : _83169 -> Prop, forall x : _83169, (@IN _83169 x (fun y : _83169 => p y)) = (p x)).
