Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2309273 : forall x : int, (int_mul (int_sgn x) (int_abs x)) = x.
