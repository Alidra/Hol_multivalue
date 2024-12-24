Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1384312 : (forall x : real, (real_neg x) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x)) /\ (forall x : real, forall y : real, (real_sub x y) = (real_add x (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y))).
