Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1602653 : forall x : real, forall y : real, forall z : real, (real_lt (real_of_num (NUMERAL 0)) z) -> (real_lt (real_mul z x) (real_mul z y)) = (real_lt x y).