Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2306723 : forall x : int, forall y : int, (int_neg (int_sub x y)) = (int_sub y x).
