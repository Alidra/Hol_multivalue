Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1587738 : forall x : real, forall y : real, ((real_mul x y) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_inv y) = x.
