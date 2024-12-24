Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1321215 : (nadd_eq (nadd_inv (nadd_of_num (NUMERAL 0))) (nadd_of_num (NUMERAL 0))) = ((hreal_inv (hreal_of_num (NUMERAL 0))) = (hreal_of_num (NUMERAL 0))).
