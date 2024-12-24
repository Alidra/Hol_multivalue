Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2288126 : forall x : int, (int_abs x) = (int_of_real (real_abs (real_of_int x))).
