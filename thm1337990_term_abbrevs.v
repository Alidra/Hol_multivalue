Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x1)).
