Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (x0 : int) := @eq real (real_of_int (int_pow x0 (NUMERAL (BIT1 0)))).
Definition term8 (x0 : int) := int_pow x0 (NUMERAL (BIT1 0)).
Definition term9 := forall y0 : int, (int_pow y0 (NUMERAL (BIT1 0))) = y0.
Definition term2 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term1 (x0 : int) := real_pow (real_of_int x0) (NUMERAL (BIT1 0)).
Definition term6 (x0 : int) := @eq real (real_pow (real_of_int x0) (NUMERAL (BIT1 0))).
Definition term0 (x0 : int) := (fun y0 : real => (real_pow y0 (NUMERAL (BIT1 0))) = y0) (real_of_int x0).
Definition term4 (x0 : int) := real_of_int (int_pow x0 (NUMERAL (BIT1 0))).
Definition term3 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term5 := NUMERAL (BIT1 0).
