Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2299824 : forall x : int, (real_abs (real_of_int x)) = (real_of_int (int_abs x)).
