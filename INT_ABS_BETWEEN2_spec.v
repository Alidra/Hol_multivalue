Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300215 : forall x0 : int, forall x : int, forall y0 : int, forall y : int, ((int_lt x0 y0) /\ ((int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub x x0))) (int_sub y0 x0)) /\ (int_lt (int_mul (int_of_num (NUMERAL (BIT0 (BIT1 0)))) (int_abs (int_sub y y0))) (int_sub y0 x0)))) -> int_lt x y.
