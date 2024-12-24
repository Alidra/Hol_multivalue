Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : int) := fun y0 : int => exists y1 : int, y0 = (int_mul x0 y1).
Definition term4 (x0 : int) (x1 : int) := exists y0 : int, x0 = (int_mul x1 y0).
Definition term8 (x0 : int) (x1 : int) := (fun y0 : int => (int_divides x0 y0) = (exists y1 : int, y0 = (int_mul x0 y1))) x1.
Definition term7 (x0 : int) := (fun y0 : int => forall y1 : int, (int_divides y0 y1) = (exists y2 : int, y1 = (int_mul y0 y2))) x0.
Definition term1 (x0 : int) := (fun y0 : int => fun y1 : int => exists y2 : int, y1 = (int_mul y0 y2)) x0.
Definition term0 := fun y0 : int => fun y1 : int => exists y2 : int, y1 = (int_mul y0 y2).
Definition term3 (x0 : int) (x1 : int) := (fun y0 : int => exists y1 : int, y0 = (int_mul x0 y1)) x1.
Definition term10 := forall y0 : int, forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2)).
Definition term6 := forall y0 : int, forall y1 : int, (int_divides y0 y1) = (exists y2 : int, y1 = (int_mul y0 y2)).
Definition term9 (x0 : int) := forall y0 : int, (int_divides y0 x0) = (exists y1 : int, x0 = (int_mul y0 y1)).
Definition term5 (x0 : int) := forall y0 : int, (int_divides x0 y0) = (exists y1 : int, y0 = (int_mul x0 y1)).
