Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_eq y0 y1) = ((mk_hreal (nadd_eq y0)) = (mk_hreal (nadd_eq y1)))) x0.
Definition term0 := forall y0 : nadd, forall y1 : nadd, (nadd_eq y0 y1) = ((mk_hreal (nadd_eq y0)) = (mk_hreal (nadd_eq y1))).
Definition term2 (x0 : nadd) := forall y0 : nadd, (nadd_eq x0 y0) = ((mk_hreal (nadd_eq x0)) = (mk_hreal (nadd_eq y0))).
Definition term3 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => (nadd_eq x0 y0) = ((mk_hreal (nadd_eq x0)) = (mk_hreal (nadd_eq y0)))) x1.
