Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416504 : (forall x : int, (int_neg x) = (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) x)) /\ (forall x : int, forall y : int, (int_sub x y) = (int_add x (int_mul (int_neg (int_of_num (NUMERAL (BIT1 0)))) y))).
