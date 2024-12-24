Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_eq x0 y0) = ((mk_real (treal_eq x0)) = (mk_real (treal_eq y0)))) x1.
Definition term1 (x0 : prod hreal hreal) := mk_real (treal_eq x0).
