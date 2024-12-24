Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (a0 : Type') (x0 : a0 -> real) (x1 : real) := forall y0 : a0 -> Prop, (@sum a0 y0 (fun y1 : a0 => real_mul (x0 y1) x1)) = (real_mul (@sum a0 y0 x0) x1).
Definition term31 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term27 (a0 : Type') := forall y0 : a0 -> real, forall y1 : real, forall y2 : a0 -> Prop, (@sum a0 y2 (fun y3 : a0 => real_mul y1 (y0 y3))) = (real_mul y1 (@sum a0 y2 y0)).
Definition term26 (a0 : Type') := forall y0 : a0 -> real, forall y1 : real, forall y2 : a0 -> Prop, (@sum a0 y2 (fun y3 : a0 => real_mul (y0 y3) y1)) = (real_mul (@sum a0 y2 y0) y1).
Definition term33 := fun y0 : real => True.
Definition term8 (x0 : real) := forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0).
Definition term0 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : real, forall y2 : a0 -> Prop, (@sum a0 y2 (fun y3 : a0 => real_mul y1 (y0 y3))) = (real_mul y1 (@sum a0 y2 y0))) x0.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := real_mul (@sum a0 x0 x1) x2.
Definition term9 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => real_mul x1 (x2 y0)).
Definition term11 (a0 : Type') (x0 : real) (x1 : a0 -> real) (x2 : a0) := real_mul x0 (x1 x2).
Definition term38 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> real, x0.
Definition term32 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term34 := forall y0 : real, True.
Definition term35 (x0 : Prop) := forall y0 : real, x0.
Definition term4 (a0 : Type') (x0 : real) (x1 : a0 -> real) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@sum a0 y0 (fun y1 : a0 => real_mul x0 (x1 y1))) = (real_mul x0 (@sum a0 y0 x1))) x2.
Definition term25 (a0 : Type') := fun y0 : a0 -> real => forall y1 : real, forall y2 : a0 -> Prop, (@sum a0 y2 (fun y3 : a0 => real_mul y1 (y0 y3))) = (real_mul y1 (@sum a0 y2 y0)).
Definition term24 (a0 : Type') := fun y0 : a0 -> real => forall y1 : real, forall y2 : a0 -> Prop, (@sum a0 y2 (fun y3 : a0 => real_mul (y0 y3) y1)) = (real_mul (@sum a0 y2 y0) y1).
Definition term23 (a0 : Type') (x0 : a0 -> real) := forall y0 : real, forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_mul (x0 y2) y0)) = (real_mul (@sum a0 y1 x0) y0).
Definition term1 (a0 : Type') (x0 : a0 -> real) := forall y0 : real, forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_mul y0 (x0 y2))) = (real_mul y0 (@sum a0 y1 x0)).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := @eq real (@sum a0 x0 (fun y0 : a0 => real_mul (x1 y0) x2)).
Definition term12 (a0 : Type') (x0 : a0 -> real) (x1 : real) := fun y0 : a0 => real_mul (x0 y0) x1.
Definition term6 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_mul x0 (@sum a0 x1 x2).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0 -> real) := @eq real (@sum a0 x0 (fun y0 : a0 => real_mul x1 (x2 y0))).
Definition term21 (a0 : Type') (x0 : a0 -> real) := fun y0 : real => forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_mul (x0 y2) y0)) = (real_mul (@sum a0 y1 x0) y0).
Definition term7 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0.
Definition term22 (a0 : Type') (x0 : a0 -> real) := fun y0 : real => forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_mul y0 (x0 y2))) = (real_mul y0 (@sum a0 y1 x0)).
Definition term29 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term36 (a0 : Type') := fun y0 : a0 -> real => True.
Definition term2 (a0 : Type') (x0 : a0 -> real) (x1 : real) := (fun y0 : real => forall y1 : a0 -> Prop, (@sum a0 y1 (fun y2 : a0 => real_mul y0 (x0 y2))) = (real_mul y0 (@sum a0 y1 x0))) x1.
Definition term13 (a0 : Type') (x0 : real) (x1 : a0 -> real) := fun y0 : a0 => real_mul x0 (x1 y0).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : real) := @sum a0 x0 (fun y0 : a0 => real_mul (x1 y0) x2).
Definition term18 (a0 : Type') (x0 : a0 -> real) (x1 : real) := fun y0 : a0 -> Prop => (@sum a0 y0 (fun y1 : a0 => real_mul (x0 y1) x1)) = (real_mul (@sum a0 y0 x0) x1).
Definition term19 (a0 : Type') (x0 : real) (x1 : a0 -> real) := fun y0 : a0 -> Prop => (@sum a0 y0 (fun y1 : a0 => real_mul x0 (x1 y1))) = (real_mul x0 (@sum a0 y0 x1)).
Definition term28 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) (x2 : a0 -> real) := @eq real (real_mul x0 (@sum a0 x1 x2)).
Definition term3 (a0 : Type') (x0 : real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, (@sum a0 y0 (fun y1 : a0 => real_mul x0 (x1 y1))) = (real_mul x0 (@sum a0 y0 x1)).
Definition term10 (a0 : Type') (x0 : a0 -> real) (x1 : a0) (x2 : real) := real_mul (x0 x1) x2.
Definition term37 (a0 : Type') := forall y0 : a0 -> real, True.
Definition term30 (a0 : Type') := forall y0 : a0 -> Prop, True.
