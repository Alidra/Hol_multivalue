Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nadd) := fun y0 : nadd => (nadd_eq x0) = (nadd_eq y0).
Definition term1 (x0 : nadd) := exists y0 : nadd, (nadd_eq x0) = (nadd_eq y0).
Definition term0 (x0 : nadd) := (fun y0 : nadd -> Prop => exists y1 : nadd, y0 = (nadd_eq y1)) (nadd_eq x0).
