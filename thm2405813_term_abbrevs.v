Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := int_of_num (NUMERAL 0).
Definition term3 (x0 : int) := (fun y0 : int => (int_add (int_neg y0) y0) = (int_of_num (NUMERAL 0))) x0.
Definition term6 (x0 : nat) := @eq int (int_add (int_neg (int_of_num x0)) (int_of_num x0)).
Definition term7 := @eq int (int_of_num (NUMERAL 0)).
Definition term10 (x0 : nat) := @eq int (int_add (int_of_num x0) (int_neg (int_of_num x0))).
Definition term5 (x0 : nat) := int_add (int_neg (int_of_num x0)) (int_of_num x0).
Definition term0 (x0 : int) := (fun y0 : int => (int_add y0 (int_neg y0)) = (int_of_num (NUMERAL 0))) x0.
Definition term4 (x0 : int) := int_add (int_neg x0) x0.
Definition term9 (x0 : nat) := int_add (int_of_num x0) (int_neg (int_of_num x0)).
Definition term11 (x0 : nat) := ((int_add (int_neg (int_of_num x0)) (int_of_num x0)) = (int_of_num (NUMERAL 0))) /\ ((int_add (int_of_num x0) (int_neg (int_of_num x0))) = (int_of_num (NUMERAL 0))).
Definition term8 (x0 : nat) := and ((int_add (int_neg (int_of_num x0)) (int_of_num x0)) = (int_of_num (NUMERAL 0))).
Definition term1 (x0 : int) := int_add x0 (int_neg x0).
