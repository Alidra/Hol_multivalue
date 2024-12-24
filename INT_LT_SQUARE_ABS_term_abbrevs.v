Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (x0 : int) := real_lt (real_of_int (int_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term8 (x0 : int) := real_lt (real_of_int (int_abs x0)).
Definition term4 (x0 : int) (x1 : int) := real_lt (real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (real_of_int x1) (NUMERAL (BIT0 (BIT1 0)))).
Definition term6 (x0 : int) := real_of_int (int_abs x0).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : real => (real_lt (real_abs (real_of_int x0)) (real_abs y0)) = (real_lt (real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_int x1).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : real, (real_lt (real_abs y0) (real_abs y1)) = (real_lt (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_int x0).
Definition term10 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term1 (x0 : int) := forall y0 : real, (real_lt (real_abs (real_of_int x0)) (real_abs y0)) = (real_lt (real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term24 (x0 : int) := forall y0 : int, (int_lt (int_abs x0) (int_abs y0)) = (int_lt (int_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (int_pow y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term19 (x0 : int) := real_lt (real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term25 := forall y0 : int, forall y1 : int, (int_lt (int_abs y0) (int_abs y1)) = (int_lt (int_pow y0 (NUMERAL (BIT0 (BIT1 0)))) (int_pow y1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term14 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term9 (x0 : int) (x1 : int) := real_lt (real_of_int (int_abs x0)) (real_of_int (int_abs x1)).
Definition term18 := NUMERAL (BIT0 (BIT1 0)).
Definition term13 (x0 : int) (x1 : int) := @eq Prop (int_lt (int_abs x0) (int_abs x1)).
Definition term22 (x0 : int) (x1 : int) := int_lt (int_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (int_pow x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term11 (x0 : int) (x1 : int) := int_lt (int_abs x0) (int_abs x1).
Definition term21 (x0 : int) (x1 : int) := real_lt (real_of_int (int_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_of_int (int_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term3 (x0 : int) (x1 : int) := real_lt (real_abs (real_of_int x0)) (real_abs (real_of_int x1)).
Definition term5 (x0 : int) := real_abs (real_of_int x0).
Definition term23 (x0 : int) := int_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term15 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term16 (x0 : int) := real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term17 (x0 : int) := real_of_int (int_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term7 (x0 : int) := real_lt (real_abs (real_of_int x0)).
Definition term12 (x0 : int) (x1 : int) := @eq Prop (real_lt (real_abs (real_of_int x0)) (real_abs (real_of_int x1))).
