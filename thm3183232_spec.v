Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3183232 : forall {_83152 : Type'} (p : _83152 -> Prop) (x : _83152), ((exists y : _83152, @SETSPEC _83152 x (p y) y) = (p x)) = ((@GSPEC _83152 (fun v : _83152 => exists y : _83152, @SETSPEC _83152 v (p y) y) x) = (p x)).
