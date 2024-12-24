Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1550986 : forall x0 : real, forall x : real, forall y0 : real, forall y : real, ((real_lt x0 y0) /\ ((real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub x x0))) (real_sub y0 x0)) /\ (real_lt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub y y0))) (real_sub y0 x0)))) -> real_lt x y.
