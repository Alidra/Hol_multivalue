Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term24 (x0 : int) (x1 : int) := forall y0 : int, (@eq2 int x0 x1 (int_mod y0)) = (exists y1 : int, (int_sub x0 x1) = (int_mul y0 y1)).
Definition term11 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (int_mod x0 y0 y1) = (int_divides x0 (int_sub y0 y1))) x1.
Definition term30 := fun y0 : int => forall y1 : int, forall y2 : int, (@eq2 int y0 y1 (int_mod y2)) = (exists y3 : int, (int_sub y0 y1) = (int_mul y2 y3)).
Definition term3 (x0 : int) (x1 : int) := exists y0 : int, x0 = (int_mul x1 y0).
Definition term28 (x0 : int) := fun y0 : int => forall y1 : int, (@eq2 int x0 y0 (int_mod y1)) = (exists y2 : int, (int_sub x0 y0) = (int_mul y1 y2)).
Definition term26 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term23 := fun y0 : int => True.
Definition term0 (x0 : int) := (fun y0 : int => forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))) x0.
Definition term9 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (int_mod y0 y1 y2) = (int_divides y0 (int_sub y1 y2))) x0.
Definition term17 (x0 : int) (x1 : int) (x2 : int) := @eq Prop (@eq2 int x0 x1 (int_mod x2)).
Definition term21 (x0 : int) (x1 : int) (x2 : int) := @eq Prop (((exists y0 : int, (int_sub x0 x1) = (int_mul x2 y0)) = (exists y0 : int, (int_sub x0 x1) = (int_mul x2 y0))) = True).
Definition term13 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_mod x0 x1 y0) = (int_divides x0 (int_sub x1 y0))) x2.
Definition term8 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (@eq2 a0 x1 y0 x0) = (x0 x1 y0)) x2.
Definition term6 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0, (@eq2 a0 y0 y1 x0) = (x0 y0 y1)) x1.
Definition term18 (x0 : int) (x1 : int) (x2 : int) := @eq Prop (exists y0 : int, (int_sub x0 x1) = (int_mul x2 y0)).
Definition term20 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((fun y0 : Prop => y0 = True) ((exists y0 : int, (int_sub x0 x1) = (int_mul x2 y0)) = (exists y0 : int, (int_sub x0 x1) = (int_mul x2 y0)))).
Definition term16 (x0 : int) (x1 : int) (x2 : int) := exists y0 : int, (int_sub x0 x1) = (int_mul x2 y0).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : int => (int_divides y0 x0) = (exists y1 : int, x0 = (int_mul y0 y1))) x1.
Definition term27 (x0 : Prop) := forall y0 : int, x0.
Definition term12 (x0 : int) (x1 : int) := forall y0 : int, (int_mod x0 x1 y0) = (int_divides x0 (int_sub x1 y0)).
Definition term31 := forall y0 : int, forall y1 : int, forall y2 : int, (@eq2 int y0 y1 (int_mod y2)) = (exists y3 : int, (int_sub y0 y1) = (int_mul y2 y3)).
Definition term29 (x0 : int) := forall y0 : int, forall y1 : int, (@eq2 int x0 y0 (int_mod y1)) = (exists y2 : int, (int_sub x0 y0) = (int_mul y1 y2)).
Definition term10 (x0 : int) := forall y0 : int, forall y1 : int, (int_mod x0 y0 y1) = (int_divides x0 (int_sub y0 y1)).
Definition term15 (x0 : int) (x1 : int) (x2 : int) := @eq2 int x0 x1 (int_mod x2).
Definition term14 (x0 : int) (x1 : int) (x2 : int) := int_divides x0 (int_sub x1 x2).
Definition term25 := forall y0 : int, True.
Definition term5 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0, forall y1 : a0, (@eq2 a0 y0 y1 x0) = (x0 y0 y1).
Definition term7 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := forall y0 : a0, (@eq2 a0 x1 y0 x0) = (x0 x1 y0).
Definition term22 (x0 : int) (x1 : int) := fun y0 : int => (@eq2 int x0 x1 (int_mod y0)) = (exists y1 : int, (int_sub x0 x1) = (int_mul y0 y1)).
Definition term19 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : Prop => y0 = True) ((exists y0 : int, (int_sub x0 x1) = (int_mul x2 y0)) = (exists y0 : int, (int_sub x0 x1) = (int_mul x2 y0))).
Definition term4 (a0 : Type') (x0 : type1402 a0) := (fun y0 : type1402 a0 => forall y1 : a0, forall y2 : a0, (@eq2 a0 y1 y2 y0) = (y0 y1 y2)) x0.
Definition term1 (x0 : int) := forall y0 : int, (int_divides y0 x0) = (exists y1 : int, x0 = (int_mul y0 y1)).
