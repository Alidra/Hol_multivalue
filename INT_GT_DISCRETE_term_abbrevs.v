Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term48 := fun y0 : int => forall y1 : int, (int_gt y0 y1) = (int_ge y0 (int_add y1 (int_of_num (NUMERAL (BIT1 0))))).
Definition term14 := fun y0 : int => forall y1 : int, (int_le y0 y1) = (real_le (real_of_int y0) (real_of_int y1)).
Definition term5 := fun y0 : int => forall y1 : int, (int_lt y0 y1) = (real_lt (real_of_int y0) (real_of_int y1)).
Definition term47 (x0 : int) := forall y0 : int, (int_lt y0 x0) = (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term45 (x0 : int) := fun y0 : int => (int_lt y0 x0) = (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term35 (x0 : int) (x1 : int) := real_gt (real_of_int x0) (real_of_int x1).
Definition term38 (x0 : int) (x1 : int) := int_ge x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))).
Definition term39 (x0 : int) (x1 : int) := real_ge (real_of_int x0) (real_of_int (int_add x1 (int_of_num (NUMERAL (BIT1 0))))).
Definition term2 (x0 : int) := fun y0 : int => (real_lt (real_of_int x0) (real_of_int y0)) = (int_lt x0 y0).
Definition term52 (x0 : int) := (fun y0 : int => forall y1 : int, (int_lt y0 y1) = (int_le (int_add y0 (int_of_num (NUMERAL (BIT1 0)))) y1)) x0.
Definition term32 (x0 : int) := (fun y0 : int => forall y1 : int, (int_gt y0 y1) = (real_gt (real_of_int y0) (real_of_int y1))) x0.
Definition term28 (x0 : int) := (fun y0 : int => forall y1 : int, (int_ge y0 y1) = (real_ge (real_of_int y0) (real_of_int y1))) x0.
Definition term20 (x0 : int) := (fun y0 : int => forall y1 : int, (real_le (real_of_int y0) (real_of_int y1)) = (int_le y0 y1)) x0.
Definition term18 (x0 : int) := (fun y0 : int => forall y1 : int, (real_lt (real_of_int y0) (real_of_int y1)) = (int_lt y0 y1)) x0.
Definition term1 (x0 : int) := fun y0 : int => (int_lt x0 y0) = (real_lt (real_of_int x0) (real_of_int y0)).
Definition term27 (x0 : real) (x1 : real) := (fun y0 : real => (real_ge y0 x0) = (real_le x0 y0)) x1.
Definition term24 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt y0 x0) = (real_lt x0 y0)) x1.
Definition term42 (x0 : int) := real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term37 (x0 : int) (x1 : int) := @eq Prop (int_lt x0 x1).
Definition term41 (x0 : int) (x1 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x1).
Definition term26 (x0 : real) := forall y0 : real, (real_ge y0 x0) = (real_le x0 y0).
Definition term23 (x0 : real) := forall y0 : real, (real_gt y0 x0) = (real_lt x0 y0).
Definition term46 (x0 : int) := forall y0 : int, (int_gt x0 y0) = (int_ge x0 (int_add y0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term13 (x0 : int) := forall y0 : int, (real_le (real_of_int x0) (real_of_int y0)) = (int_le x0 y0).
Definition term4 (x0 : int) := forall y0 : int, (real_lt (real_of_int x0) (real_of_int y0)) = (int_lt x0 y0).
Definition term33 (x0 : int) := forall y0 : int, (int_gt x0 y0) = (real_gt (real_of_int x0) (real_of_int y0)).
Definition term29 (x0 : int) := forall y0 : int, (int_ge x0 y0) = (real_ge (real_of_int x0) (real_of_int y0)).
Definition term12 (x0 : int) := forall y0 : int, (int_le x0 y0) = (real_le (real_of_int x0) (real_of_int y0)).
Definition term3 (x0 : int) := forall y0 : int, (int_lt x0 y0) = (real_lt (real_of_int x0) (real_of_int y0)).
Definition term43 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term0 (x0 : int) (x1 : int) := real_lt (real_of_int x0) (real_of_int x1).
Definition term53 (x0 : int) := forall y0 : int, (int_lt x0 y0) = (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) y0).
Definition term11 (x0 : int) := fun y0 : int => (real_le (real_of_int x0) (real_of_int y0)) = (int_le x0 y0).
Definition term19 (x0 : int) (x1 : int) := (fun y0 : int => (real_lt (real_of_int x0) (real_of_int y0)) = (int_lt x0 y0)) x1.
Definition term31 (x0 : int) (x1 : int) := real_ge (real_of_int x0) (real_of_int x1).
Definition term51 := forall y0 : int, forall y1 : int, (int_lt y1 y0) = (int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) y0).
Definition term50 := forall y0 : int, forall y1 : int, (int_gt y0 y1) = (int_ge y0 (int_add y1 (int_of_num (NUMERAL (BIT1 0))))).
Definition term17 := forall y0 : int, forall y1 : int, (real_le (real_of_int y0) (real_of_int y1)) = (int_le y0 y1).
Definition term16 := forall y0 : int, forall y1 : int, (int_le y0 y1) = (real_le (real_of_int y0) (real_of_int y1)).
Definition term8 := forall y0 : int, forall y1 : int, (real_lt (real_of_int y0) (real_of_int y1)) = (int_lt y0 y1).
Definition term7 := forall y0 : int, forall y1 : int, (int_lt y0 y1) = (real_lt (real_of_int y0) (real_of_int y1)).
Definition term25 (x0 : real) := (fun y0 : real => forall y1 : real, (real_ge y1 y0) = (real_le y0 y1)) x0.
Definition term22 (x0 : real) := (fun y0 : real => forall y1 : real, (real_gt y1 y0) = (real_lt y0 y1)) x0.
Definition term40 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term49 := fun y0 : int => forall y1 : int, (int_lt y1 y0) = (int_le (int_add y1 (int_of_num (NUMERAL (BIT1 0)))) y0).
Definition term15 := fun y0 : int => forall y1 : int, (real_le (real_of_int y0) (real_of_int y1)) = (int_le y0 y1).
Definition term6 := fun y0 : int => forall y1 : int, (real_lt (real_of_int y0) (real_of_int y1)) = (int_lt y0 y1).
Definition term9 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term34 (x0 : int) (x1 : int) := (fun y0 : int => (int_gt x0 y0) = (real_gt (real_of_int x0) (real_of_int y0))) x1.
Definition term54 (x0 : int) (x1 : int) := (fun y0 : int => (int_lt x0 y0) = (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) y0)) x1.
Definition term36 (x0 : int) (x1 : int) := @eq Prop (int_gt x0 x1).
Definition term21 (x0 : int) (x1 : int) := (fun y0 : int => (real_le (real_of_int x0) (real_of_int y0)) = (int_le x0 y0)) x1.
Definition term10 (x0 : int) := fun y0 : int => (int_le x0 y0) = (real_le (real_of_int x0) (real_of_int y0)).
Definition term30 (x0 : int) (x1 : int) := (fun y0 : int => (int_ge x0 y0) = (real_ge (real_of_int x0) (real_of_int y0))) x1.
Definition term44 (x0 : int) := fun y0 : int => (int_gt x0 y0) = (int_ge x0 (int_add y0 (int_of_num (NUMERAL (BIT1 0))))).
