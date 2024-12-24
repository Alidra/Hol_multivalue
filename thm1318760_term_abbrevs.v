Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : hreal -> Prop) := (fun y0 : hreal -> Prop => (forall y1 : nadd, y0 (mk_hreal (nadd_eq y1))) = (forall y1 : hreal, y0 y1)) x0.
Definition term2 (x0 : hreal -> Prop) := forall y0 : hreal, x0 y0.
Definition term1 (x0 : hreal -> Prop) := forall y0 : nadd, x0 (mk_hreal (nadd_eq y0)).
