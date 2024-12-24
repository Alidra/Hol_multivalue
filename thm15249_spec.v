Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem15249 : forall {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975), True = ((@COND _2975 (x = x) y z) = y).
