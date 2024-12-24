Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term27 (a0 : Type') := forall y0 : a0, ~ ((@None a0) = (@Some a0 y0)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a1 => forall y1 : a0 -> a1, exists y2 : type1159 a0 a1, ((y2 (@None a0)) = y0) /\ (forall y3 : a0, (y2 (@Some a0 y3)) = (y1 y3))) x0.
Definition term23 := @eq nat (NUMERAL 0).
Definition term11 (a0 : Type') := fun y0 : a0 => NUMERAL (BIT1 0).
Definition term0 (a0 : Type') (x0 : type1161 a0) := forall y0 : a0, (x0 (@Some a0 y0)) = (NUMERAL (BIT1 0)).
Definition term12 (a0 : Type') (x0 : a0) := (fun y0 : a0 => NUMERAL (BIT1 0)) x0.
Definition term18 (a0 : Type') (x0 : type1161 a0) := ((x0 (@None a0)) = (NUMERAL 0)) /\ (forall y0 : a0, (x0 (@Some a0 y0)) = ((fun y1 : a0 => NUMERAL (BIT1 0)) y0)).
Definition term20 (a0 : Type') := fun y0 : type1161 a0 => ((y0 (@None a0)) = (NUMERAL 0)) /\ (forall y1 : a0, (y0 (@Some a0 y1)) = (NUMERAL (BIT1 0))).
Definition term19 (a0 : Type') := fun y0 : type1161 a0 => ((y0 (@None a0)) = (NUMERAL 0)) /\ (forall y1 : a0, (y0 (@Some a0 y1)) = ((fun y2 : a0 => NUMERAL (BIT1 0)) y1)).
Definition term22 (a0 : Type') (x0 : type1161 a0) := @eq nat (x0 (@None a0)).
Definition term1 (a0 : Type') (x0 : type1161 a0) (x1 : a0) := (fun y0 : a0 => (x0 (@Some a0 y0)) = (NUMERAL (BIT1 0))) x1.
Definition term15 (a0 : Type') (x0 : type1161 a0) := fun y0 : a0 => (x0 (@Some a0 y0)) = (NUMERAL (BIT1 0)).
Definition term21 (a0 : Type') := exists y0 : type1161 a0, ((y0 (@None a0)) = (NUMERAL 0)) /\ (forall y1 : a0, (y0 (@Some a0 y1)) = (NUMERAL (BIT1 0))).
Definition term10 (a0 : Type') := exists y0 : type1161 a0, ((y0 (@None a0)) = (NUMERAL 0)) /\ (forall y1 : a0, (y0 (@Some a0 y1)) = ((fun y2 : a0 => NUMERAL (BIT1 0)) y1)).
Definition term4 (a0 : Type') (x0 : type1161 a0) := ((x0 (@None a0)) = (NUMERAL 0)) /\ (forall y0 : a0, (x0 (@Some a0 y0)) = (NUMERAL (BIT1 0))).
Definition term25 (a0 : Type') (x0 : a0) := ((@None a0) = (@Some a0 x0)) -> False.
Definition term13 (a0 : Type') (x0 : type1161 a0) (x1 : a0) := @eq nat (x0 (@Some a0 x1)).
Definition term2 (a0 : Type') (x0 : type1161 a0) (x1 : a0) := x0 (@Some a0 x1).
Definition term24 := S (Nat.add 0 0).
Definition term17 (a0 : Type') (x0 : type1161 a0) := and ((x0 (@None a0)) = (NUMERAL 0)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => exists y1 : type1159 a0 a1, ((y1 (@None a0)) = x0) /\ (forall y2 : a0, (y1 (@Some a0 y2)) = (y0 y2))) x1.
Definition term16 (a0 : Type') (x0 : type1161 a0) := forall y0 : a0, (x0 (@Some a0 y0)) = ((fun y1 : a0 => NUMERAL (BIT1 0)) y0).
Definition term14 (a0 : Type') (x0 : type1161 a0) := fun y0 : a0 => (x0 (@Some a0 y0)) = ((fun y1 : a0 => NUMERAL (BIT1 0)) y0).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a1) := forall y0 : a0 -> a1, exists y1 : type1159 a0 a1, ((y1 (@None a0)) = x0) /\ (forall y2 : a0, (y1 (@Some a0 y2)) = (y0 y2)).
Definition term9 (a0 : Type') (x0 : nat) (x1 : a0 -> nat) := exists y0 : type1161 a0, ((y0 (@None a0)) = x0) /\ (forall y1 : a0, (y0 (@Some a0 y1)) = (x1 y1)).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0 -> a1) := exists y0 : type1159 a0 a1, ((y0 (@None a0)) = x0) /\ (forall y1 : a0, (y0 (@Some a0 y1)) = (x1 y1)).
Definition term26 (a0 : Type') (x0 : a0) := ~ ((@None a0) = (@Some a0 x0)).
Definition term3 := NUMERAL (BIT1 0).
