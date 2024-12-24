Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nadd) := hreal_inv (mk_hreal (nadd_eq x0)).
Definition term1 (x0 : nadd) := mk_hreal (nadd_eq (nadd_inv x0)).
