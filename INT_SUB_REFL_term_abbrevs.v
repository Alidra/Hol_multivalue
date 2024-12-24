Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : int) (x1 : int) := real_of_int (int_sub x0 x1).
Definition term3 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term5 (x0 : int) := real_of_int (int_sub x0 x0).
Definition term9 := real_of_int (int_of_num (NUMERAL 0)).
Definition term2 := real_of_num (NUMERAL 0).
Definition term10 := int_of_num (NUMERAL 0).
Definition term0 (x0 : int) := (fun y0 : real => (real_sub y0 y0) = (real_of_num (NUMERAL 0))) (real_of_int x0).
Definition term7 (x0 : int) := @eq real (real_of_int (int_sub x0 x0)).
Definition term8 (x0 : nat) := real_of_int (int_of_num x0).
Definition term1 (x0 : int) := real_sub (real_of_int x0) (real_of_int x0).
Definition term11 := forall y0 : int, (int_sub y0 y0) = (int_of_num (NUMERAL 0)).
Definition term6 (x0 : int) := @eq real (real_sub (real_of_int x0) (real_of_int x0)).
