Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3184707 : forall {_83169 : Type'}, (forall p : _83169 -> Prop, forall x : _83169, (@IN _83169 x (fun y : _83169 => p y)) = (p x)) = (forall p : _83169 -> Prop, forall x : _83169, (@IN _83169 x (fun y : _83169 => p y)) = (p x)).
