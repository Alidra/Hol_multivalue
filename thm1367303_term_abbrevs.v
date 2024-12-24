Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := real_of_num (NUMERAL 0).
Definition term11 (x0 : nat) := ((real_add (real_neg (real_of_num x0)) (real_of_num x0)) = (real_of_num (NUMERAL 0))) /\ ((real_add (real_of_num x0) (real_neg (real_of_num x0))) = (real_of_num (NUMERAL 0))).
Definition term9 (x0 : nat) := real_add (real_of_num x0) (real_neg (real_of_num x0)).
Definition term10 (x0 : nat) := @eq real (real_add (real_of_num x0) (real_neg (real_of_num x0))).
Definition term0 (x0 : real) := (fun y0 : real => (real_add y0 (real_neg y0)) = (real_of_num (NUMERAL 0))) x0.
Definition term5 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term4 (x0 : real) := real_add (real_neg x0) x0.
Definition term7 := @eq real (real_of_num (NUMERAL 0)).
Definition term3 (x0 : real) := (fun y0 : real => (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term8 (x0 : nat) := and ((real_add (real_neg (real_of_num x0)) (real_of_num x0)) = (real_of_num (NUMERAL 0))).
Definition term1 (x0 : real) := real_add x0 (real_neg x0).
Definition term6 (x0 : nat) := @eq real (real_add (real_neg (real_of_num x0)) (real_of_num x0)).
