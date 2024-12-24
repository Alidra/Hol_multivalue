Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (x0 : real) (x1 : nat) := @COND real True (real_pow x0 x1).
Definition term21 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term23 := fun y0 : real => forall y1 : nat, (real_pow y0 y1) = (real_zpow y0 (int_of_num y1)).
Definition term24 := fun y0 : real => True.
Definition term12 (x0 : real) (x1 : nat) := @COND real (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) (real_pow x0 (num_of_int (int_of_num x1))).
Definition term26 := forall y0 : real, True.
Definition term27 (x0 : Prop) := forall y0 : real, x0.
Definition term19 (x0 : real) := forall y0 : nat, (real_pow x0 y0) = (real_zpow x0 (int_of_num y0)).
Definition term25 := forall y0 : real, forall y1 : nat, (real_pow y0 y1) = (real_zpow y0 (int_of_num y1)).
Definition term17 (x0 : real) := fun y0 : nat => (real_pow x0 y0) = (real_zpow x0 (int_of_num y0)).
Definition term7 (x0 : real) (x1 : int) := @COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))).
Definition term2 (x0 : nat) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) x0.
Definition term6 (x0 : real) (x1 : int) := (fun y0 : int => (real_zpow x0 y0) = (@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_pow x0 (num_of_int y0)) (real_inv (real_pow x0 (num_of_int (int_neg y0)))))) x1.
Definition term20 := forall y0 : nat, True.
Definition term9 (x0 : real) (x1 : nat) := @COND real (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) (real_pow x0 (num_of_int (int_of_num x1))) (real_inv (real_pow x0 (num_of_int (int_neg (int_of_num x1))))).
Definition term10 (x0 : nat) := @COND real (int_le (int_of_num (NUMERAL 0)) (int_of_num x0)).
Definition term18 := fun y0 : nat => True.
Definition term3 (x0 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term14 (x0 : real) (x1 : nat) := real_inv (real_pow x0 (num_of_int (int_neg (int_of_num x1)))).
Definition term16 (x0 : real) (x1 : nat) := @eq real (real_pow x0 x1).
Definition term1 (x0 : nat) := num_of_int (int_of_num x0).
Definition term5 (x0 : real) := forall y0 : int, (real_zpow x0 y0) = (@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_pow x0 (num_of_int y0)) (real_inv (real_pow x0 (num_of_int (int_neg y0))))).
Definition term11 (x0 : real) (x1 : nat) := real_pow x0 (num_of_int (int_of_num x1)).
Definition term4 (x0 : real) := (fun y0 : real => forall y1 : int, (real_zpow y0 y1) = (@COND real (int_le (int_of_num (NUMERAL 0)) y1) (real_pow y0 (num_of_int y1)) (real_inv (real_pow y0 (num_of_int (int_neg y1)))))) x0.
Definition term8 (x0 : real) (x1 : nat) := real_zpow x0 (int_of_num x1).
Definition term22 (x0 : Prop) := forall y0 : nat, x0.
Definition term15 (x0 : real) (x1 : nat) := @COND real True (real_pow x0 x1) (real_inv (real_pow x0 (num_of_int (int_neg (int_of_num x1))))).
Definition term0 (x0 : nat) := (fun y0 : nat => (num_of_int (int_of_num y0)) = y0) x0.
