Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 := forall y0 : real -> Prop, (forall y1 : prod hreal hreal, y0 (mk_real (treal_eq y1))) = (forall y1 : real, y0 y1).
Definition term0 := (forall y0 : real -> Prop, (forall y1 : prod hreal hreal, y0 (mk_real (treal_eq y1))) = (forall y1 : real, y0 y1)) /\ ((forall y0 : real -> Prop, (exists y1 : prod hreal hreal, y0 (mk_real (treal_eq y1))) = (exists y1 : real, y0 y1)) /\ (forall y0 : real, (mk_real (treal_eq (@ε (prod hreal hreal) (dest_real y0)))) = y0)).
Definition term2 (x0 : real -> Prop) := (fun y0 : real -> Prop => (forall y1 : prod hreal hreal, y0 (mk_real (treal_eq y1))) = (forall y1 : real, y0 y1)) x0.
