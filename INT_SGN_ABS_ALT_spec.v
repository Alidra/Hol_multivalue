Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2309297 : forall x : int, (int_mul (int_sgn x) x) = (int_abs x).
