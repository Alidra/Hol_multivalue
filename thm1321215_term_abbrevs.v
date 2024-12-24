Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 := hreal_of_num (NUMERAL 0).
Definition term3 := mk_hreal (nadd_eq (nadd_of_num (NUMERAL 0))).
Definition term2 := mk_hreal (nadd_eq (nadd_inv (nadd_of_num (NUMERAL 0)))).
Definition term7 (x0 : nadd) := hreal_inv (mk_hreal (nadd_eq x0)).
Definition term6 (x0 : nadd) := mk_hreal (nadd_eq (nadd_inv x0)).
Definition term13 := @eq hreal (hreal_inv (hreal_of_num (NUMERAL 0))).
Definition term12 := @eq hreal (mk_hreal (nadd_eq (nadd_inv (nadd_of_num (NUMERAL 0))))).
Definition term8 := hreal_inv (mk_hreal (nadd_eq (nadd_of_num (NUMERAL 0)))).
Definition term5 := nadd_of_num (NUMERAL 0).
Definition term9 (x0 : nat) := mk_hreal (nadd_eq (nadd_of_num x0)).
Definition term4 := nadd_inv (nadd_of_num (NUMERAL 0)).
Definition term0 (x0 : nadd) := mk_hreal (nadd_eq x0).
Definition term1 := nadd_eq (nadd_inv (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)).
Definition term11 := hreal_inv (hreal_of_num (NUMERAL 0)).
