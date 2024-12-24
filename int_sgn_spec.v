Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2288988 : forall x : int, (int_sgn x) = (int_of_real (real_sgn (real_of_int x))).
