Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1102442 : forall {_25350 _25351 : Type'} (h : _25351) (f : _25351 -> _25350 -> _25350) (t : list _25351) (b : _25350), ((@ITLIST _25350 _25351 f (@nil _25351) b) = b) /\ ((@ITLIST _25350 _25351 f (@cons _25351 h t) b) = (f h (@ITLIST _25350 _25351 f t b))).