Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3184714 : forall {_83152 : Type'}, forall p : _83152 -> Prop, forall x : _83152, (@GSPEC _83152 (fun v : _83152 => exists y : _83152, @SETSPEC _83152 v (p y) y) x) = (p x).
