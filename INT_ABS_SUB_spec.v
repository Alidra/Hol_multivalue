Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300765 : forall x : int, forall y : int, (int_abs (int_sub x y)) = (int_abs (int_sub y x)).
