Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1632551 : forall x : real, forall y : real, ((real_lt (real_of_num (NUMERAL 0)) y) /\ (real_lt (real_inv y) x)) -> real_lt (real_inv x) y.
