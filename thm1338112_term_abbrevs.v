Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : prod hreal hreal, forall y1 : prod hreal hreal, (treal_eq y0 y1) = ((mk_real (treal_eq y0)) = (mk_real (treal_eq y1))).
Definition term2 (x0 : prod hreal hreal) := forall y0 : prod hreal hreal, (treal_eq x0 y0) = ((mk_real (treal_eq x0)) = (mk_real (treal_eq y0))).
Definition term3 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := (fun y0 : prod hreal hreal => (treal_eq x0 y0) = ((mk_real (treal_eq x0)) = (mk_real (treal_eq y0)))) x1.
Definition term1 (x0 : prod hreal hreal) := (fun y0 : prod hreal hreal => forall y1 : prod hreal hreal, (treal_eq y0 y1) = ((mk_real (treal_eq y0)) = (mk_real (treal_eq y1)))) x0.
