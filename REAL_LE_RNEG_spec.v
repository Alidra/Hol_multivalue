Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1362465 : forall x : real, forall y : real, (real_le x (real_neg y)) = (real_le (real_add x y) (real_of_num (NUMERAL 0))).