Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term15 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term6 := real_of_int (int_of_num (NUMERAL 0)).
Definition term5 := real_of_num (NUMERAL 0).
Definition term13 := int_of_num (NUMERAL 0).
Definition term25 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term20 := real_add (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term36 (x0 : nat) (x1 : int) := real_le (real_of_int (int_add (int_of_num (NUMERAL (BIT1 0))) (int_mul (int_of_num x0) x1))).
Definition term9 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term34 (x0 : nat) (x1 : int) := int_mul (int_of_num x0) x1.
Definition term35 (x0 : nat) (x1 : int) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x0) (real_of_int x1))).
Definition term32 (x0 : nat) (x1 : int) := real_of_int (int_add (int_of_num (NUMERAL (BIT1 0))) (int_mul (int_of_num x0) x1)).
Definition term41 (x0 : int) := real_pow (real_of_int (int_add (int_of_num (NUMERAL (BIT1 0))) x0)).
Definition term43 (x0 : int) (x1 : nat) := real_pow (real_of_int (int_add (int_of_num (NUMERAL (BIT1 0))) x0)) x1.
Definition term7 := real_le (real_of_num (NUMERAL 0)).
Definition term31 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term48 (x0 : int) (x1 : nat) := real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x1) (real_of_int x0))) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) x1).
Definition term52 (x0 : int) (x1 : nat) := int_pow (int_add (int_of_num (NUMERAL (BIT1 0))) x0) x1.
Definition term4 (x0 : nat) := real_of_int (int_of_num x0).
Definition term54 (x0 : int) := forall y0 : nat, (int_le (int_of_num (NUMERAL 0)) x0) -> int_le (int_add (int_of_num (NUMERAL (BIT1 0))) (int_mul (int_of_num y0) x0)) (int_pow (int_add (int_of_num (NUMERAL (BIT1 0))) x0) y0).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : nat, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y1) y0)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) y0) y1)) (real_of_int x0).
Definition term49 (x0 : int) (x1 : nat) := real_le (real_of_int (int_add (int_of_num (NUMERAL (BIT1 0))) (int_mul (int_of_num x1) x0))) (real_of_int (int_pow (int_add (int_of_num (NUMERAL (BIT1 0))) x0) x1)).
Definition term30 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term53 (x0 : int) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) x0) -> int_le (int_add (int_of_num (NUMERAL (BIT1 0))) (int_mul (int_of_num x1) x0)) (int_pow (int_add (int_of_num (NUMERAL (BIT1 0))) x0) x1).
Definition term14 (x0 : int) := imp (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term28 (x0 : nat) (x1 : int) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x0) (real_of_int x1)).
Definition term55 := forall y0 : int, forall y1 : nat, (int_le (int_of_num (NUMERAL 0)) y0) -> int_le (int_add (int_of_num (NUMERAL (BIT1 0))) (int_mul (int_of_num y1) y0)) (int_pow (int_add (int_of_num (NUMERAL (BIT1 0))) y0) y1).
Definition term24 (x0 : nat) (x1 : int) := real_mul (real_of_int (int_of_num x0)) (real_of_int x1).
Definition term44 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term42 (x0 : int) (x1 : nat) := real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) x1.
Definition term38 (x0 : int) := real_add (real_of_int (int_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term21 (x0 : nat) := real_mul (real_of_num x0).
Definition term23 (x0 : nat) (x1 : int) := real_mul (real_of_num x0) (real_of_int x1).
Definition term51 (x0 : nat) (x1 : int) := int_add (int_of_num (NUMERAL (BIT1 0))) (int_mul (int_of_num x0) x1).
Definition term47 (x0 : int) := int_add (int_of_num (NUMERAL (BIT1 0))) x0.
Definition term11 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term22 (x0 : nat) := real_mul (real_of_int (int_of_num x0)).
Definition term1 (x0 : int) := forall y0 : nat, (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) (real_of_int x0))) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) y0).
Definition term16 := real_of_num (NUMERAL (BIT1 0)).
Definition term10 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term19 := real_add (real_of_num (NUMERAL (BIT1 0))).
Definition term27 (x0 : nat) (x1 : int) := real_of_int (int_mul (int_of_num x0) x1).
Definition term3 (x0 : int) (x1 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num x1) (real_of_int x0))) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) x1).
Definition term26 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term17 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term39 (x0 : int) := real_of_int (int_add (int_of_num (NUMERAL (BIT1 0))) x0).
Definition term12 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term45 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term29 (x0 : nat) (x1 : int) := real_add (real_of_int (int_of_num (NUMERAL (BIT1 0)))) (real_of_int (int_mul (int_of_num x0) x1)).
Definition term37 (x0 : int) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0).
Definition term8 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term46 (x0 : int) (x1 : nat) := real_of_int (int_pow (int_add (int_of_num (NUMERAL (BIT1 0))) x0) x1).
Definition term33 := int_of_num (NUMERAL (BIT1 0)).
Definition term40 (x0 : int) := real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)).
Definition term18 := NUMERAL (BIT1 0).
Definition term50 (x0 : int) (x1 : nat) := int_le (int_add (int_of_num (NUMERAL (BIT1 0))) (int_mul (int_of_num x1) x0)) (int_pow (int_add (int_of_num (NUMERAL (BIT1 0))) x0) x1).
Definition term2 (x0 : int) (x1 : nat) := (fun y0 : nat => (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num y0) (real_of_int x0))) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) y0)) x1.
