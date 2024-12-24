Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1102428 : forall {_25350 _25351 : Type'} (f : _25351 -> _25350 -> _25350) (b : _25350), ((fun b' : _25350 => (@ITLIST _25350 _25351 f (@nil _25351) b') = b') b) = ((@ITLIST _25350 _25351 f (@nil _25351) b) = b).
