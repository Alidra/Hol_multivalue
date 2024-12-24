Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (x0 : nat) := real_of_int (int_of_num (S x0)).
Definition term2 (x0 : nat) := real_of_num (S x0).
Definition term18 (x0 : nat) := int_of_num (S x0).
Definition term19 := forall y0 : nat, (int_add (int_of_num y0) (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (S y0)).
Definition term11 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term1 (x0 : nat) := real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term3 (x0 : nat) := real_of_int (int_of_num x0).
Definition term15 (x0 : nat) := @eq real (real_of_int (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0))))).
Definition term10 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term0 (x0 : nat) := (fun y0 : nat => (real_add (real_of_num y0) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (S y0))) x0.
Definition term17 (x0 : nat) := int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0))).
Definition term5 (x0 : nat) := real_add (real_of_int (int_of_num x0)).
Definition term4 (x0 : nat) := real_add (real_of_num x0).
Definition term6 := real_of_num (NUMERAL (BIT1 0)).
Definition term9 (x0 : nat) := real_add (real_of_int (int_of_num x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term12 (x0 : nat) := real_of_int (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))).
Definition term14 (x0 : nat) := @eq real (real_add (real_of_num x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term7 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term13 := int_of_num (NUMERAL (BIT1 0)).
Definition term8 := NUMERAL (BIT1 0).
