Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3562581 : forall {_91244 _91249 : Type'}, forall f : _91249 -> _91244, (forall x : _91249, forall y : _91249, ((f x) = (f y)) -> x = y) = (forall x : _91249, forall y : _91249, ((f x) = (f y)) = (x = y)).
