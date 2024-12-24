Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1532076 : forall x : real, real_le (real_of_num (NUMERAL 0)) (real_abs x).
