Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nadd) (x1 : nadd) := hreal_add (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1)).
Definition term1 (x0 : nadd) (x1 : nadd) := mk_hreal (nadd_eq (nadd_add x0 x1)).
