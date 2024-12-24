Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2291527 : forall x : int, (real_of_int (int_sgn x)) = (real_sgn (real_of_int x)).
