Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2319812 : forall x : int, forall y : int, (int_sub x y) = (int_add x (int_neg y)).
