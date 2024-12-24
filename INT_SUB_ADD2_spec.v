Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2310151 : forall x : int, forall y : int, (int_add y (int_sub x y)) = x.
