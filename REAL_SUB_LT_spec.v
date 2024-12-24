Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1376486 : forall x : real, forall y : real, (real_lt (real_of_num (NUMERAL 0)) (real_sub x y)) = (real_lt y x).
