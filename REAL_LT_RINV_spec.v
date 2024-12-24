Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1632664 : forall x : real, forall y : real, ((real_lt (real_of_num (NUMERAL 0)) x) /\ (real_lt x (real_inv y))) -> real_lt y (real_inv x).
