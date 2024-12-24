Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 := forall y0 : nadd, (nadd_inv y0) = (@COND nadd (nadd_eq y0 (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv y0))).
Definition term0 := fun y0 : nadd => @COND nadd (nadd_eq y0 (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv y0)).
Definition term1 (x0 : nadd) := (fun y0 : nadd => @COND nadd (nadd_eq y0 (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv y0))) x0.
Definition term2 (x0 : nadd) := @COND nadd (nadd_eq x0 (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv x0)).
Definition term4 (x0 : nadd) := (fun y0 : nadd => (nadd_inv y0) = (@COND nadd (nadd_eq y0 (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0)) (mk_nadd (nadd_rinv y0)))) x0.
