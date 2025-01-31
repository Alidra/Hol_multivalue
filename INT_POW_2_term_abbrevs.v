Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : int) := real_mul (real_of_int x0) (real_of_int x0).
Definition term9 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term11 (x0 : int) := real_of_int (int_mul x0 x0).
Definition term13 := forall y0 : int, (int_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (int_mul y0 y0).
Definition term0 (x0 : int) := (fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) (real_of_int x0).
Definition term8 (x0 : int) := @eq real (real_of_int (int_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term3 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term6 := NUMERAL (BIT0 (BIT1 0)).
Definition term10 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term12 (x0 : int) := int_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term4 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term1 (x0 : int) := real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term5 (x0 : int) := real_of_int (int_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term7 (x0 : int) := @eq real (real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0)))).
