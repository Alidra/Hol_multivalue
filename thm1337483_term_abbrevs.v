Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : prod hreal hreal) := fun y0 : prod hreal hreal => (treal_eq x0) = (treal_eq y0).
Definition term0 (x0 : prod hreal hreal) := (fun y0 : type1233 => exists y1 : prod hreal hreal, y0 = (treal_eq y1)) (treal_eq x0).
Definition term1 (x0 : prod hreal hreal) := exists y0 : prod hreal hreal, (treal_eq x0) = (treal_eq y0).
