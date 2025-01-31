Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : prod hreal hreal) := real_neg (mk_real (treal_eq x0)).
Definition term1 (x0 : prod hreal hreal) := mk_real (treal_eq (treal_neg x0)).
