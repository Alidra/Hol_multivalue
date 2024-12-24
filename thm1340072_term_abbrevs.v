Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := mk_real (treal_eq (treal_inv (treal_of_num (NUMERAL 0)))).
Definition term13 := @eq real (real_inv (real_of_num (NUMERAL 0))).
Definition term10 := real_of_num (NUMERAL 0).
Definition term12 := @eq real (mk_real (treal_eq (treal_inv (treal_of_num (NUMERAL 0))))).
Definition term11 := real_inv (real_of_num (NUMERAL 0)).
Definition term4 := treal_inv (treal_of_num (NUMERAL 0)).
Definition term5 := treal_of_num (NUMERAL 0).
Definition term7 (x0 : prod hreal hreal) := real_inv (mk_real (treal_eq x0)).
Definition term1 := treal_eq (treal_inv (treal_of_num (NUMERAL 0))) (treal_of_num (NUMERAL 0)).
Definition term9 (x0 : nat) := mk_real (treal_eq (treal_of_num x0)).
Definition term6 (x0 : prod hreal hreal) := mk_real (treal_eq (treal_inv x0)).
Definition term0 (x0 : prod hreal hreal) := mk_real (treal_eq x0).
Definition term8 := real_inv (mk_real (treal_eq (treal_of_num (NUMERAL 0)))).
Definition term3 := mk_real (treal_eq (treal_of_num (NUMERAL 0))).
