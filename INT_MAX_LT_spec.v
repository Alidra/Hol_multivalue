Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305351 : forall x : int, forall y : int, forall z : int, (int_lt (int_max x y) z) = ((int_lt x z) /\ (int_lt y z)).
