Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term39 := @SUBSET real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (real_le (real_of_num (NUMERAL 0)) y1) y1)) (@UNIV real).
Definition term15 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term40 := imp (@SUBSET real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (real_le (real_of_num (NUMERAL 0)) y1) y1)) (@UNIV real)).
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term5 (x0 : real) := (~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (real_le x0 y1) y1)))) -> (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (real_le x0 y1) y1))) = False.
Definition term42 := real_of_num (NUMERAL 0).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) -> (@SUBSET a0 x1 x0) -> @FINITE a0 x1.
Definition term35 := @GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (real_le (real_of_num (NUMERAL 0)) y1) y1).
Definition term32 := (@FINITE real (@UNIV real)) -> forall y0 : real -> Prop, (@SUBSET real y0 (@UNIV real)) -> @FINITE real y0.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> @FINITE a0 x1.
Definition term24 (a0 : Type') := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1.
Definition term14 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@SUBSET a0 x0 y0) -> @FINITE a0 x0.
Definition term41 := @FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (real_le (real_of_num (NUMERAL 0)) y1) y1)).
Definition term6 (x0 : real) := @FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (real_le x0 y1) y1)).
Definition term16 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@SUBSET a0 y0 y1) -> @FINITE a0 y0.
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term29 (x0 : real -> Prop) := ~ (@FINITE real x0).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term26 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1) x0.
Definition term33 := forall y0 : real -> Prop, (@SUBSET real y0 (@UNIV real)) -> @FINITE real y0.
Definition term31 (x0 : real -> Prop) := (@FINITE real x0) -> forall y0 : real -> Prop, (@SUBSET real y0 x0) -> @FINITE real y0.
Definition term23 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> forall y0 : a0 -> Prop, (@SUBSET a0 y0 x0) -> @FINITE a0 y0.
Definition term36 := (@SUBSET real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (real_le (real_of_num (NUMERAL 0)) y1) y1)) (@UNIV real)) -> @FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (real_le (real_of_num (NUMERAL 0)) y1) y1)).
Definition term37 := ((@SUBSET real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (real_le (real_of_num (NUMERAL 0)) y1) y1)) (@UNIV real)) -> @FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (real_le (real_of_num (NUMERAL 0)) y1) y1))) -> False.
Definition term19 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@SUBSET a0 y0 y1) -> @FINITE a0 y0) x0.
Definition term2 := forall y0 : real, ~ (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 (real_le y0 y2) y2))).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => @SUBSET a0 y0 (@UNIV a0)) x0.
Definition term34 := (fun y0 : real -> Prop => (@SUBSET real y0 (@UNIV real)) -> @FINITE real y0) (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (real_le (real_of_num (NUMERAL 0)) y1) y1)).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@SUBSET a0 x0 y0) -> @FINITE a0 x0.
Definition term22 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@SUBSET a0 y0 x0) -> @FINITE a0 y0.
Definition term7 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term18 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@SUBSET a0 y0 y1) -> @FINITE a0 y0.
Definition term17 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term43 := (@FINITE real (@UNIV real)) -> False.
Definition term30 := ~ (@FINITE real (@UNIV real)).
Definition term3 (x0 : real) := (fun y0 : real => ~ (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 (real_le y0 y2) y2)))) x0.
Definition term1 := (forall y0 : real, ~ (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 (real_le y0 y2) y2)))) /\ ((forall y0 : real, ~ (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 (real_lt y2 y0) y2)))) /\ ((forall y0 : real, ~ (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 (real_le y2 y0) y2)))) /\ ((forall y0 : real, forall y1 : real, (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((real_lt y0 y3) /\ (real_lt y3 y1)) y3))) = (real_le y1 y0)) /\ ((forall y0 : real, forall y1 : real, (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((real_le y0 y3) /\ (real_lt y3 y1)) y3))) = (real_le y1 y0)) /\ ((forall y0 : real, forall y1 : real, (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((real_lt y0 y3) /\ (real_le y3 y1)) y3))) = (real_le y1 y0)) /\ (forall y0 : real, forall y1 : real, (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((real_le y0 y3) /\ (real_le y3 y1)) y3))) = (real_le y1 y0))))))).
Definition term25 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@SUBSET a0 y0 y1) -> @FINITE a0 y0) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1.
Definition term38 := ~ ((@SUBSET real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (real_le (real_of_num (NUMERAL 0)) y1) y1)) (@UNIV real)) -> @FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (real_le (real_of_num (NUMERAL 0)) y1) y1))).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@SUBSET a0 x0 y0) -> @FINITE a0 x0) x1.
Definition term4 (x0 : real) := ~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (real_le x0 y1) y1))).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@INFINITE a0 y0) = (~ (@FINITE a0 y0))) x0.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x1 x0) -> @FINITE a0 x1.
