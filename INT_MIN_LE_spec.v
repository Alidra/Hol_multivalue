Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305662 : forall x : int, forall y : int, forall z : int, (int_le (int_min x y) z) = ((int_le x z) \/ (int_le y z)).
