Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (int_mod x0 y0 y1) = (int_divides x0 (int_sub y0 y1))) x1.
Definition term3 (x0 : int) (x1 : int) := (fun y0 : int => fun y1 : int => int_divides x0 (int_sub y0 y1)) x1.
Definition term10 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (int_mod y0 y1 y2) = (int_divides y0 (int_sub y1 y2))) x0.
Definition term12 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_mod x0 x1 y0) = (int_divides x0 (int_sub x1 y0))) x2.
Definition term2 (x0 : int) := fun y0 : int => fun y1 : int => int_divides x0 (int_sub y0 y1).
Definition term7 (x0 : int) (x1 : int) := forall y0 : int, (int_mod x0 x1 y0) = (int_divides x0 (int_sub x1 y0)).
Definition term9 := forall y0 : int, forall y1 : int, forall y2 : int, (int_mod y0 y1 y2) = (int_divides y0 (int_sub y1 y2)).
Definition term8 (x0 : int) := forall y0 : int, forall y1 : int, (int_mod x0 y0 y1) = (int_divides x0 (int_sub y0 y1)).
Definition term6 (x0 : int) (x1 : int) (x2 : int) := int_divides x0 (int_sub x1 x2).
Definition term0 := fun y0 : int => fun y1 : int => fun y2 : int => int_divides y0 (int_sub y1 y2).
Definition term5 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => int_divides x0 (int_sub x1 y0)) x2.
Definition term1 (x0 : int) := (fun y0 : int => fun y1 : int => fun y2 : int => int_divides y0 (int_sub y1 y2)) x0.
Definition term4 (x0 : int) (x1 : int) := fun y0 : int => int_divides x0 (int_sub x1 y0).
