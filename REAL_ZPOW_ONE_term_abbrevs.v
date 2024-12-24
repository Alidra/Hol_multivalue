Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : Prop) := forall y0 : a0, (@COND a0 x0 y0 y0) = y0.
Definition term24 := fun y0 : int => (real_zpow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term18 (x0 : int) := real_inv (real_pow (real_of_num (NUMERAL (BIT1 0))) (num_of_int (int_neg x0))).
Definition term4 (x0 : nat) := real_pow (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term28 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term25 := fun y0 : int => True.
Definition term12 (x0 : int) := real_pow (real_of_num (NUMERAL (BIT1 0))) (num_of_int x0).
Definition term10 (x0 : int) := real_zpow (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term9 (x0 : real) (x1 : int) := @COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))).
Definition term11 (x0 : int) := @COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_pow (real_of_num (NUMERAL (BIT1 0))) (num_of_int x0)) (real_inv (real_pow (real_of_num (NUMERAL (BIT1 0))) (num_of_int (int_neg x0)))).
Definition term13 (x0 : int) := @COND real (int_le (int_of_num (NUMERAL 0)) x0).
Definition term26 := forall y0 : int, (real_zpow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term8 (x0 : real) (x1 : int) := (fun y0 : int => (real_zpow x0 y0) = (@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_pow x0 (num_of_int y0)) (real_inv (real_pow x0 (num_of_int (int_neg y0)))))) x1.
Definition term29 (x0 : Prop) := forall y0 : int, x0.
Definition term15 (x0 : int) := @COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term22 (x0 : int) := @eq real (real_zpow (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term27 := forall y0 : int, True.
Definition term2 (a0 : Type') (x0 : Prop) (x1 : a0) := (fun y0 : a0 => (@COND a0 x0 y0 y0) = y0) x1.
Definition term16 (x0 : int) := real_pow (real_of_num (NUMERAL (BIT1 0))) (num_of_int (int_neg x0)).
Definition term17 (x0 : int) := num_of_int (int_neg x0).
Definition term7 (x0 : real) := forall y0 : int, (real_zpow x0 y0) = (@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_pow x0 (num_of_int y0)) (real_inv (real_pow x0 (num_of_int (int_neg y0))))).
Definition term5 := real_of_num (NUMERAL (BIT1 0)).
Definition term3 (x0 : nat) := (fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term19 := real_inv (real_of_num (NUMERAL (BIT1 0))).
Definition term6 (x0 : real) := (fun y0 : real => forall y1 : int, (real_zpow y0 y1) = (@COND real (int_le (int_of_num (NUMERAL 0)) y1) (real_pow y0 (num_of_int y1)) (real_inv (real_pow y0 (num_of_int (int_neg y1)))))) x0.
Definition term23 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term14 (x0 : int) := @COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_pow (real_of_num (NUMERAL (BIT1 0))) (num_of_int x0)).
Definition term21 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term0 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0, (@COND a0 y0 y1 y1) = y1) x0.
Definition term20 (x0 : int) := @COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
