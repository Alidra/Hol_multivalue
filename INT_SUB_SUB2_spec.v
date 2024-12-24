Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2310500 : forall x : int, forall y : int, (int_sub x (int_sub x y)) = y.
