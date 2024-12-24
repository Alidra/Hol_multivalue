Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 := @COND nadd True (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv (nadd_of_num (NUMERAL 0)))).
Definition term12 := nadd_eq (nadd_inv (nadd_of_num (NUMERAL 0))).
Definition term2 (x0 : nadd) := @COND nadd (nadd_eq x0 (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv x0)).
Definition term5 := nadd_of_num (NUMERAL 0).
Definition term10 := mk_nadd (nadd_rinv (nadd_of_num (NUMERAL 0))).
Definition term7 := @COND nadd (nadd_eq (nadd_of_num (NUMERAL 0)) (nadd_of_num (NUMERAL 0))).
Definition term0 (x0 : nadd) := (fun y0 : nadd => nadd_eq y0 y0) x0.
Definition term3 := nadd_inv (nadd_of_num (NUMERAL 0)).
Definition term4 := @COND nadd (nadd_eq (nadd_of_num (NUMERAL 0)) (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv (nadd_of_num (NUMERAL 0)))).
Definition term9 := @COND nadd True (nadd_of_num (NUMERAL 0)).
Definition term14 := nadd_eq (nadd_inv (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)).
Definition term6 := nadd_eq (nadd_of_num (NUMERAL 0)) (nadd_of_num (NUMERAL 0)).
Definition term8 := @COND nadd (nadd_eq (nadd_of_num (NUMERAL 0)) (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)).
Definition term1 (x0 : nadd) := (fun y0 : nadd => (nadd_inv y0) = (@COND nadd (nadd_eq y0 (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv y0)))) x0.
Definition term13 := nadd_eq (nadd_of_num (NUMERAL 0)).
