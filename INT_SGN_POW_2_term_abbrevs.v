Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : int) := real_sgn (real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term9 (x0 : int) := real_sgn (real_of_int x0).
Definition term11 (x0 : int) := real_of_int (int_sgn (int_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term14 (x0 : int) := @eq real (real_of_int (int_sgn (int_pow x0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term16 (x0 : int) := real_of_int (int_abs x0).
Definition term20 (x0 : int) := int_sgn (int_abs x0).
Definition term3 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term19 (x0 : int) := int_sgn (int_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term10 (x0 : int) := real_of_int (int_sgn x0).
Definition term7 := NUMERAL (BIT0 (BIT1 0)).
Definition term17 (x0 : int) := real_sgn (real_of_int (int_abs x0)).
Definition term18 (x0 : int) := real_of_int (int_sgn (int_abs x0)).
Definition term8 (x0 : int) := real_sgn (real_of_int (int_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term15 (x0 : int) := real_abs (real_of_int x0).
Definition term12 (x0 : int) := int_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term4 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term5 (x0 : int) := real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term6 (x0 : int) := real_of_int (int_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term0 (x0 : int) := (fun y0 : real => (real_sgn (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = (real_sgn (real_abs y0))) (real_of_int x0).
Definition term13 (x0 : int) := @eq real (real_sgn (real_pow (real_of_int x0) (NUMERAL (BIT0 (BIT1 0))))).
Definition term21 := forall y0 : int, (int_sgn (int_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = (int_sgn (int_abs y0)).
Definition term2 (x0 : int) := real_sgn (real_abs (real_of_int x0)).
