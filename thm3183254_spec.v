Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3183254 : forall {_83169 : Type'} (p : _83169 -> Prop) (x : _83169), (@IN _83169 x (fun y : _83169 => p y)) = (p x).
