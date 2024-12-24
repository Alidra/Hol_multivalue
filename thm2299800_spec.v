Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2299800 : forall x : int, (real_sgn (real_of_int x)) = (real_of_int (int_sgn x)).
