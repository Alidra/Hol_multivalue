Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (x0 : nat) := ((int_abs (int_neg (int_of_num x0))) = (int_of_num x0)) /\ ((int_abs (int_of_num x0)) = (int_of_num x0)).
Definition term5 (x0 : nat) := @eq int (int_abs (int_neg (int_of_num x0))).
Definition term8 (x0 : nat) := @eq int (int_abs (int_of_num x0)).
Definition term3 (x0 : int) := int_abs (int_neg x0).
Definition term2 (x0 : int) := (fun y0 : int => (int_abs (int_neg y0)) = (int_abs y0)) x0.
Definition term7 (x0 : nat) := and ((int_abs (int_neg (int_of_num x0))) = (int_of_num x0)).
Definition term1 (x0 : nat) := int_abs (int_of_num x0).
Definition term6 (x0 : nat) := @eq int (int_of_num x0).
Definition term0 (x0 : nat) := (fun y0 : nat => (int_abs (int_of_num y0)) = (int_of_num y0)) x0.
Definition term4 (x0 : nat) := int_abs (int_neg (int_of_num x0)).
