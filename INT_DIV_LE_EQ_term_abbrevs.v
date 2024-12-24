Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term31 (x0 : int) (x1 : int) (x2 : int) := ((int_lt (int_of_num (NUMERAL 0)) x2) -> ((int_le (div x0 x2) x1) = (int_lt x0 (int_mul x2 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))))) = True) -> ((int_lt (int_of_num (NUMERAL 0)) x2) -> (int_le (div x0 x2) x1) = (int_lt x0 (int_mul x2 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))))) = ((int_lt (int_of_num (NUMERAL 0)) x2) -> True).
Definition term40 (x0 : int) := fun y0 : int => forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) x0) -> (int_le (div y0 x0) y1) = (int_lt y0 (int_mul x0 (int_add y1 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) x0) -> (int_lt (div y0 x0) y1) = (int_lt y0 (int_mul x0 y1))) x1.
Definition term42 := fun y0 : int => forall y1 : int, forall y2 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_le (div y1 y0) y2) = (int_lt y1 (int_mul y0 (int_add y2 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term29 (x0 : int) (x1 : int) (x2 : int) := @eq Prop (int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term38 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term35 := fun y0 : int => True.
Definition term9 (x0 : int) := (fun y0 : int => forall y1 : int, (int_le y0 y1) = (int_lt y0 (int_add y1 (int_of_num (NUMERAL (BIT1 0)))))) x0.
Definition term0 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_lt (div y1 y0) y2) = (int_lt y1 (int_mul y0 y2))) x0.
Definition term17 (x0 : int) (x1 : int) (x2 : int) := int_le (div x0 x1) x2.
Definition term5 (x0 : int) (x1 : int) (x2 : int) := (int_lt (int_of_num (NUMERAL 0)) x1) -> (int_lt (div x0 x1) x2) = (int_lt x0 (int_mul x1 x2)).
Definition term10 (x0 : int) := forall y0 : int, (int_le x0 y0) = (int_lt x0 (int_add y0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term36 (x0 : int) (x1 : int) := forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) x1) -> (int_le (div x0 x1) y0) = (int_lt x0 (int_mul x1 (int_add y0 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term3 (x0 : int) (x1 : int) := forall y0 : int, (int_lt (int_of_num (NUMERAL 0)) x1) -> (int_lt (div x0 x1) y0) = (int_lt x0 (int_mul x1 y0)).
Definition term33 (x0 : int) := (int_lt (int_of_num (NUMERAL 0)) x0) -> True.
Definition term34 (x0 : int) (x1 : int) := fun y0 : int => (int_lt (int_of_num (NUMERAL 0)) x1) -> (int_le (div x0 x1) y0) = (int_lt x0 (int_mul x1 (int_add y0 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term18 (x0 : int) (x1 : int) (x2 : int) := int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))).
Definition term19 (x0 : int) (x1 : int) (x2 : int) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((int_lt (int_of_num (NUMERAL 0)) x1) = y0) -> (y0 -> ((int_le (div x0 x1) x2) = (int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))))) = y1) -> ((int_lt (int_of_num (NUMERAL 0)) x1) -> (int_le (div x0 x1) x2) = (int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))))) = (y0 -> y1)) x3.
Definition term25 (x0 : int) (x1 : int) (x2 : int) := int_lt (div x0 x1) (int_add x2 (int_of_num (NUMERAL (BIT1 0)))).
Definition term13 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term26 (x0 : int) (x1 : int) (x2 : int) := (int_lt (int_of_num (NUMERAL 0)) x1) -> (int_lt (div x0 x1) (int_add x2 (int_of_num (NUMERAL (BIT1 0))))) = (int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term22 (x0 : int) (x1 : int) (x2 : int) (x3 : Prop) (x4 : Prop) := ((int_lt (int_of_num (NUMERAL 0)) x1) = x3) -> (x3 -> ((int_le (div x0 x1) x2) = (int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))))) = x4) -> ((int_lt (int_of_num (NUMERAL 0)) x1) -> (int_le (div x0 x1) x2) = (int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))))) = (x3 -> x4).
Definition term6 (x0 : int) := int_lt (int_of_num (NUMERAL 0)) x0.
Definition term23 (x0 : int) (x1 : int) (x2 : int) (x3 : Prop) := ((int_lt (int_of_num (NUMERAL 0)) x2) = (int_lt (int_of_num (NUMERAL 0)) x2)) -> ((int_lt (int_of_num (NUMERAL 0)) x2) -> ((int_le (div x0 x2) x1) = (int_lt x0 (int_mul x2 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))))) = x3) -> ((int_lt (int_of_num (NUMERAL 0)) x2) -> (int_le (div x0 x2) x1) = (int_lt x0 (int_mul x2 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))))) = ((int_lt (int_of_num (NUMERAL 0)) x2) -> x3).
Definition term7 (x0 : int) (x1 : int) (x2 : int) := int_lt (div x0 x1) x2.
Definition term39 (x0 : Prop) := forall y0 : int, x0.
Definition term43 := forall y0 : int, forall y1 : int, forall y2 : int, (int_lt (int_of_num (NUMERAL 0)) y0) -> (int_le (div y1 y0) y2) = (int_lt y1 (int_mul y0 (int_add y2 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term41 (x0 : int) := forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) x0) -> (int_le (div y0 x0) y1) = (int_lt y0 (int_mul x0 (int_add y1 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term1 (x0 : int) := forall y0 : int, forall y1 : int, (int_lt (int_of_num (NUMERAL 0)) x0) -> (int_lt (div y0 x0) y1) = (int_lt y0 (int_mul x0 y1)).
Definition term27 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term20 (x0 : int) (x1 : int) (x2 : int) (x3 : Prop) := forall y0 : Prop, ((int_lt (int_of_num (NUMERAL 0)) x1) = x3) -> (x3 -> ((int_le (div x0 x1) x2) = (int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))))) = y0) -> ((int_lt (int_of_num (NUMERAL 0)) x1) -> (int_le (div x0 x1) x2) = (int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))))) = (x3 -> y0).
Definition term14 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term32 (x0 : int) (x1 : int) (x2 : int) := (int_lt (int_of_num (NUMERAL 0)) x1) -> (int_le (div x0 x1) x2) = (int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term16 (x0 : int) (x1 : int) (x2 : int) := forall y0 : Prop, forall y1 : Prop, ((int_lt (int_of_num (NUMERAL 0)) x1) = y0) -> (y0 -> ((int_le (div x0 x1) x2) = (int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))))) = y1) -> ((int_lt (int_of_num (NUMERAL 0)) x1) -> (int_le (div x0 x1) x2) = (int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))))) = (y0 -> y1).
Definition term15 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term24 (x0 : int) (x1 : int) (x2 : int) (x3 : Prop) := ((int_lt (int_of_num (NUMERAL 0)) x2) -> ((int_le (div x0 x2) x1) = (int_lt x0 (int_mul x2 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))))) = x3) -> ((int_lt (int_of_num (NUMERAL 0)) x2) -> (int_le (div x0 x2) x1) = (int_lt x0 (int_mul x2 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))))) = ((int_lt (int_of_num (NUMERAL 0)) x2) -> x3).
Definition term4 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_lt (int_of_num (NUMERAL 0)) x1) -> (int_lt (div x0 x1) y0) = (int_lt x0 (int_mul x1 y0))) x2.
Definition term21 (x0 : int) (x1 : int) (x2 : int) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((int_lt (int_of_num (NUMERAL 0)) x1) = x3) -> (x3 -> ((int_le (div x0 x1) x2) = (int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))))) = y0) -> ((int_lt (int_of_num (NUMERAL 0)) x1) -> (int_le (div x0 x1) x2) = (int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))))) = (x3 -> y0)) x4.
Definition term37 := forall y0 : int, True.
Definition term30 (x0 : int) (x1 : int) (x2 : int) := (int_lt (int_of_num (NUMERAL 0)) x1) -> ((int_le (div x0 x1) x2) = (int_lt x0 (int_mul x1 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))))) = True.
Definition term11 (x0 : int) (x1 : int) := (fun y0 : int => (int_le x0 y0) = (int_lt x0 (int_add y0 (int_of_num (NUMERAL (BIT1 0)))))) x1.
Definition term28 (x0 : int) (x1 : int) (x2 : int) := @eq Prop (int_le (div x0 x1) x2).
Definition term8 (x0 : int) (x1 : int) (x2 : int) := int_lt x0 (int_mul x1 x2).
Definition term12 (x0 : int) (x1 : int) := int_lt x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))).
