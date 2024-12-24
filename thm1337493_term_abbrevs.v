Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : type1233) := exists y0 : prod hreal hreal, x0 = (treal_eq y0).
Definition term4 (x0 : type1233) := @eq Prop (exists y0 : prod hreal hreal, x0 = (treal_eq y0)).
Definition term1 (x0 : type1233) := dest_real (mk_real x0).
Definition term0 (x0 : type1233) := (fun y0 : type1233 => exists y1 : prod hreal hreal, y0 = (treal_eq y1)) x0.
Definition term3 (x0 : type1233) := @eq Prop ((fun y0 : type1233 => exists y1 : prod hreal hreal, y0 = (treal_eq y1)) x0).
