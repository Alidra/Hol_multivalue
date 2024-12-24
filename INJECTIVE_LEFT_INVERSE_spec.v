Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3576367 : forall {_91597 _91600 : Type'} (f : _91597 -> _91600), (forall x : _91597, forall y : _91597, ((f x) = (f y)) -> x = y) = (exists g : _91600 -> _91597, forall x : _91597, (g (f x)) = x).
