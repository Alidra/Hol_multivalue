Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : int) (x1 : int) := forall y0 : int, (@eq2 int x0 x1 (int_mod y0)) = (exists y1 : int, (int_sub x0 x1) = (int_mul y0 y1)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (@eq2 int x0 y0 (int_mod y1)) = (exists y2 : int, (int_sub x0 y0) = (int_mul y1 y2))) x1.
Definition term0 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (@eq2 int y0 y1 (int_mod y2)) = (exists y3 : int, (int_sub y0 y1) = (int_mul y2 y3))) x0.
Definition term4 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (@eq2 int x0 x1 (int_mod y0)) = (exists y1 : int, (int_sub x0 x1) = (int_mul y0 y1))) x2.
Definition term1 (x0 : int) := forall y0 : int, forall y1 : int, (@eq2 int x0 y0 (int_mod y1)) = (exists y2 : int, (int_sub x0 y0) = (int_mul y1 y2)).
