Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1373458 : forall x : real, forall y : real, ((real_le (real_of_num (NUMERAL 0)) x) /\ (real_le (real_of_num (NUMERAL 0)) y)) -> real_le (real_of_num (NUMERAL 0)) (real_add x y).