Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2284714 : forall x : int, forall y : int, (real_of_int (int_add x y)) = (real_add (real_of_int x) (real_of_int y)).
