Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1102422 : forall {_25350 _25351 : Type'}, forall h : _25351, forall f : _25351 -> _25350 -> _25350, forall t : list _25351, forall b : _25350, (@ITLIST _25350 _25351 f (@cons _25351 h t) b) = (f h (@ITLIST _25350 _25351 f t b)).
