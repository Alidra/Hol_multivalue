Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @iterate real a1 real_add (@IMAGE a0 a1 x0 x1).
Definition term47 (a0 : Type') (a1 : Type') (x0 : type1627) := (@monoidal real x0) -> forall y0 : a1 -> real, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, forall y4 : a0, ((@IN a0 y3 y2) /\ ((@IN a0 y4 y2) /\ ((~ (y3 = y4)) /\ ((y1 y3) = (y1 y4))))) -> (y0 (y1 y3)) = (@neutral real x0))) -> (@iterate real a1 x0 (@IMAGE a0 a1 y1 y2) y0) = (@iterate real a0 x0 y2 (@o a0 a1 real y0 y1)).
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1400 a2) := (@monoidal a2 x0) -> forall y0 : a1 -> a2, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, forall y4 : a0, ((@IN a0 y3 y2) /\ ((@IN a0 y4 y2) /\ ((~ (y3 = y4)) /\ ((y1 y3) = (y1 y4))))) -> (y0 (y1 y3)) = (@neutral a2 x0))) -> (@iterate a2 a1 x0 (@IMAGE a0 a1 y1 y2) y0) = (@iterate a2 a0 x0 y2 (@o a0 a1 a2 y0 y1)).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) (x3 : a0) := forall y0 : a0, ((@IN a0 x3 x0) /\ ((@IN a0 y0 x0) /\ ((~ (x3 = y0)) /\ ((x2 x3) = (x2 y0))))) -> (x1 (x2 x3)) = (real_of_num (NUMERAL 0)).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) (x3 : a0) := fun y0 : a0 => ((@IN a0 x3 x0) /\ ((@IN a0 y0 x0) /\ ((~ (x3 = y0)) /\ ((x2 x3) = (x2 y0))))) -> (x1 (x2 x3)) = (real_of_num (NUMERAL 0)).
Definition term6 := real_of_num (NUMERAL 0).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a1 -> real) (x3 : a0 -> a1) (x4 : a0) := ((@IN a0 x4 x0) /\ ((@IN a0 x1 x0) /\ ((~ (x4 = x1)) /\ ((x3 x4) = (x3 x1))))) -> (x2 (x3 x4)) = (@neutral real real_add).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a1 -> real) := fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((~ (y2 = y3)) /\ ((y0 y2) = (y0 y3))))) -> (x0 (y0 y2)) = (@neutral real real_add))) -> (@iterate real a1 real_add (@IMAGE a0 a1 y0 y1) x0) = (@iterate real a0 real_add y1 (@o a0 a1 real x0 y0)).
Definition term39 (a0 : Type') (a1 : Type') (x0 : a1 -> real) := fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((~ (y2 = y3)) /\ ((y0 y2) = (y0 y3))))) -> (x0 (y0 y2)) = (real_of_num (NUMERAL 0)))) -> (@sum a1 (@IMAGE a0 a1 y0 y1) x0) = (@sum a0 y1 (@o a0 a1 real x0 y0)).
Definition term46 (a0 : Type') (a1 : Type') := forall y0 : a1 -> real, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, forall y4 : a0, ((@IN a0 y3 y2) /\ ((@IN a0 y4 y2) /\ ((~ (y3 = y4)) /\ ((y1 y3) = (y1 y4))))) -> (y0 (y1 y3)) = (@neutral real real_add))) -> (@iterate real a1 real_add (@IMAGE a0 a1 y1 y2) y0) = (@iterate real a0 real_add y2 (@o a0 a1 real y0 y1)).
Definition term45 (a0 : Type') (a1 : Type') := forall y0 : a1 -> real, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, forall y4 : a0, ((@IN a0 y3 y2) /\ ((@IN a0 y4 y2) /\ ((~ (y3 = y4)) /\ ((y1 y3) = (y1 y4))))) -> (y0 (y1 y3)) = (real_of_num (NUMERAL 0)))) -> (@sum a1 (@IMAGE a0 a1 y1 y2) y0) = (@sum a0 y2 (@o a0 a1 real y0 y1)).
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1400 a2) := forall y0 : a1 -> a2, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, forall y4 : a0, ((@IN a0 y3 y2) /\ ((@IN a0 y4 y2) /\ ((~ (y3 = y4)) /\ ((y1 y3) = (y1 y4))))) -> (y0 (y1 y3)) = (@neutral a2 x0))) -> (@iterate a2 a1 x0 (@IMAGE a0 a1 y1 y2) y0) = (@iterate a2 a0 x0 y2 (@o a0 a1 a2 y0 y1)).
Definition term34 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) := ((@FINITE a0 x0) /\ (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ ((~ (y0 = y1)) /\ ((x2 y0) = (x2 y1))))) -> (x1 (x2 y0)) = (@neutral real real_add))) -> (@iterate real a1 real_add (@IMAGE a0 a1 x2 x0) x1) = (@iterate real a0 real_add x0 (@o a0 a1 real x1 x2)).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) := @sum a0 x0 (@o a0 a1 real x1 x2).
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') := forall y0 : type1400 a2, (@monoidal a2 y0) -> forall y1 : a1 -> a2, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, ((@FINITE a0 y3) /\ (forall y4 : a0, forall y5 : a0, ((@IN a0 y4 y3) /\ ((@IN a0 y5 y3) /\ ((~ (y4 = y5)) /\ ((y2 y4) = (y2 y5))))) -> (y1 (y2 y4)) = (@neutral a2 y0))) -> (@iterate a2 a1 y0 (@IMAGE a0 a1 y2 y3) y1) = (@iterate a2 a0 y0 y3 (@o a0 a1 a2 y1 y2)).
Definition term48 (a0 : Type') (a1 : Type') := (@monoidal real real_add) -> forall y0 : a1 -> real, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, forall y4 : a0, ((@IN a0 y3 y2) /\ ((@IN a0 y4 y2) /\ ((~ (y3 = y4)) /\ ((y1 y3) = (y1 y4))))) -> (y0 (y1 y3)) = (@neutral real real_add))) -> (@iterate real a1 real_add (@IMAGE a0 a1 y1 y2) y0) = (@iterate real a0 real_add y2 (@o a0 a1 real y0 y1)).
Definition term38 (a0 : Type') (a1 : Type') (x0 : a1 -> real) (x1 : a0 -> a1) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ ((~ (y1 = y2)) /\ ((x1 y1) = (x1 y2))))) -> (x0 (x1 y1)) = (@neutral real real_add))) -> (@iterate real a1 real_add (@IMAGE a0 a1 x1 y0) x0) = (@iterate real a0 real_add y0 (@o a0 a1 real x0 x1)).
Definition term37 (a0 : Type') (a1 : Type') (x0 : a1 -> real) (x1 : a0 -> a1) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ ((~ (y1 = y2)) /\ ((x1 y1) = (x1 y2))))) -> (x0 (x1 y1)) = (real_of_num (NUMERAL 0)))) -> (@sum a1 (@IMAGE a0 a1 x1 y0) x0) = (@sum a0 y0 (@o a0 a1 real x0 x1)).
Definition term44 (a0 : Type') (a1 : Type') := fun y0 : a1 -> real => forall y1 : a0 -> a1, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, forall y4 : a0, ((@IN a0 y3 y2) /\ ((@IN a0 y4 y2) /\ ((~ (y3 = y4)) /\ ((y1 y3) = (y1 y4))))) -> (y0 (y1 y3)) = (@neutral real real_add))) -> (@iterate real a1 real_add (@IMAGE a0 a1 y1 y2) y0) = (@iterate real a0 real_add y2 (@o a0 a1 real y0 y1)).
Definition term43 (a0 : Type') (a1 : Type') := fun y0 : a1 -> real => forall y1 : a0 -> a1, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, forall y4 : a0, ((@IN a0 y3 y2) /\ ((@IN a0 y4 y2) /\ ((~ (y3 = y4)) /\ ((y1 y3) = (y1 y4))))) -> (y0 (y1 y3)) = (real_of_num (NUMERAL 0)))) -> (@sum a1 (@IMAGE a0 a1 y1 y2) y0) = (@sum a0 y2 (@o a0 a1 real y0 y1)).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term32 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) := @iterate real a0 real_add x0 (@o a0 a1 real x1 x2).
Definition term4 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1400 a2) := (forall y0 : type1400 a2, (@monoidal a2 y0) -> forall y1 : a1 -> a2, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, ((@FINITE a0 y3) /\ (forall y4 : a0, forall y5 : a0, ((@IN a0 y4 y3) /\ ((@IN a0 y5 y3) /\ ((~ (y4 = y5)) /\ ((y2 y4) = (y2 y5))))) -> (y1 (y2 y4)) = (@neutral a2 y0))) -> (@iterate a2 a1 y0 (@IMAGE a0 a1 y2 y3) y1) = (@iterate a2 a0 y0 y3 (@o a0 a1 a2 y1 y2))) -> forall y0 : a1 -> a2, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, forall y4 : a0, ((@IN a0 y3 y2) /\ ((@IN a0 y4 y2) /\ ((~ (y3 = y4)) /\ ((y1 y3) = (y1 y4))))) -> (y0 (y1 y3)) = (@neutral a2 x0))) -> (@iterate a2 a1 x0 (@IMAGE a0 a1 y1 y2) y0) = (@iterate a2 a0 x0 y2 (@o a0 a1 a2 y0 y1)).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) (x3 : a0) := fun y0 : a0 => ((@IN a0 x3 x0) /\ ((@IN a0 y0 x0) /\ ((~ (x3 = y0)) /\ ((x2 x3) = (x2 y0))))) -> (x1 (x2 x3)) = (@neutral real real_add).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a1 -> real) (x1 : a0 -> a1) (x2 : a0) := x0 (x1 x2).
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) := imp ((@FINITE a0 x0) /\ (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ ((~ (y0 = y1)) /\ ((x2 y0) = (x2 y1))))) -> (x1 (x2 y0)) = (@neutral real real_add))).
Definition term23 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) := imp ((@FINITE a0 x0) /\ (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ ((~ (y0 = y1)) /\ ((x2 y0) = (x2 y1))))) -> (x1 (x2 y0)) = (real_of_num (NUMERAL 0)))).
Definition term27 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a1 -> real) := @sum a1 (@IMAGE a0 a1 x0 x1) x2.
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a1 -> real) (x3 : a0 -> a1) (x4 : a0) := ((@IN a0 x4 x0) /\ ((@IN a0 x1 x0) /\ ((~ (x4 = x1)) /\ ((x3 x4) = (x3 x1))))) -> (x2 (x3 x4)) = (real_of_num (NUMERAL 0)).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) := fun y0 : a0 => forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ ((~ (y0 = y1)) /\ ((x2 y0) = (x2 y1))))) -> (x1 (x2 y0)) = (@neutral real real_add).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) := (@FINITE a0 x0) /\ (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ ((~ (y0 = y1)) /\ ((x2 y0) = (x2 y1))))) -> (x1 (x2 y0)) = (@neutral real real_add)).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) := (@FINITE a0 x0) /\ (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ ((~ (y0 = y1)) /\ ((x2 y0) = (x2 y1))))) -> (x1 (x2 y0)) = (real_of_num (NUMERAL 0))).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> a1) (x3 : a0) := imp ((@IN a0 x1 x0) /\ ((@IN a0 x3 x0) /\ ((~ (x1 = x3)) /\ ((x2 x1) = (x2 x3))))).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a1 -> real) (x1 : a0 -> a1) (x2 : a0) := @eq real (x0 (x1 x2)).
Definition term42 (a0 : Type') (a1 : Type') (x0 : a1 -> real) := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((~ (y2 = y3)) /\ ((y0 y2) = (y0 y3))))) -> (x0 (y0 y2)) = (@neutral real real_add))) -> (@iterate real a1 real_add (@IMAGE a0 a1 y0 y1) x0) = (@iterate real a0 real_add y1 (@o a0 a1 real x0 y0)).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a1 -> real) := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((~ (y2 = y3)) /\ ((y0 y2) = (y0 y3))))) -> (x0 (y0 y2)) = (real_of_num (NUMERAL 0)))) -> (@sum a1 (@IMAGE a0 a1 y0 y1) x0) = (@sum a0 y1 (@o a0 a1 real x0 y0)).
Definition term25 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @sum a1 (@IMAGE a0 a1 x0 x1).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) := fun y0 : a0 => forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ ((~ (y0 = y1)) /\ ((x2 y0) = (x2 y1))))) -> (x1 (x2 y0)) = (real_of_num (NUMERAL 0)).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) (x3 : a0) := forall y0 : a0, ((@IN a0 x3 x0) /\ ((@IN a0 y0 x0) /\ ((~ (x3 = y0)) /\ ((x2 x3) = (x2 y0))))) -> (x1 (x2 x3)) = (@neutral real real_add).
Definition term28 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a1 -> real) := @iterate real a1 real_add (@IMAGE a0 a1 x0 x1) x2.
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) := forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ ((~ (y0 = y1)) /\ ((x2 y0) = (x2 y1))))) -> (x1 (x2 y0)) = (@neutral real real_add).
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) := forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ ((~ (y0 = y1)) /\ ((x2 y0) = (x2 y1))))) -> (x1 (x2 y0)) = (real_of_num (NUMERAL 0)).
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a1 -> real) := @eq real (@iterate real a1 real_add (@IMAGE a0 a1 x0 x1) x2).
Definition term29 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : a1 -> real) := @eq real (@sum a1 (@IMAGE a0 a1 x0 x1) x2).
Definition term5 (a0 : Type') (a1 : Type') (a2 : Type') := (forall y0 : type1400 a2, (@monoidal a2 y0) -> forall y1 : a1 -> a2, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, ((@FINITE a0 y3) /\ (forall y4 : a0, forall y5 : a0, ((@IN a0 y4 y3) /\ ((@IN a0 y5 y3) /\ ((~ (y4 = y5)) /\ ((y2 y4) = (y2 y5))))) -> (y1 (y2 y4)) = (@neutral a2 y0))) -> (@iterate a2 a1 y0 (@IMAGE a0 a1 y2 y3) y1) = (@iterate a2 a0 y0 y3 (@o a0 a1 a2 y1 y2))) -> forall y0 : type1400 a2, (@monoidal a2 y0) -> forall y1 : a1 -> a2, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, ((@FINITE a0 y3) /\ (forall y4 : a0, forall y5 : a0, ((@IN a0 y4 y3) /\ ((@IN a0 y5 y3) /\ ((~ (y4 = y5)) /\ ((y2 y4) = (y2 y5))))) -> (y1 (y2 y4)) = (@neutral a2 y0))) -> (@iterate a2 a1 y0 (@IMAGE a0 a1 y2 y3) y1) = (@iterate a2 a0 y0 y3 (@o a0 a1 a2 y1 y2)).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a1 -> real) (x1 : a0 -> a1) := fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ ((~ (y1 = y2)) /\ ((x1 y1) = (x1 y2))))) -> (x0 (x1 y1)) = (real_of_num (NUMERAL 0)))) -> (@sum a1 (@IMAGE a0 a1 x1 y0) x0) = (@sum a0 y0 (@o a0 a1 real x0 x1)).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> real) (x2 : a0 -> a1) := ((@FINITE a0 x0) /\ (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ ((~ (y0 = y1)) /\ ((x2 y0) = (x2 y1))))) -> (x1 (x2 y0)) = (real_of_num (NUMERAL 0)))) -> (@sum a1 (@IMAGE a0 a1 x2 x0) x1) = (@sum a0 x0 (@o a0 a1 real x1 x2)).
Definition term36 (a0 : Type') (a1 : Type') (x0 : a1 -> real) (x1 : a0 -> a1) := fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ ((~ (y1 = y2)) /\ ((x1 y1) = (x1 y2))))) -> (x0 (x1 y1)) = (@neutral real real_add))) -> (@iterate real a1 real_add (@IMAGE a0 a1 x1 y0) x0) = (@iterate real a0 real_add y0 (@o a0 a1 real x0 x1)).
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : type1400 a2) := (fun y0 : type1400 a2 => (@monoidal a2 y0) -> forall y1 : a1 -> a2, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, ((@FINITE a0 y3) /\ (forall y4 : a0, forall y5 : a0, ((@IN a0 y4 y3) /\ ((@IN a0 y5 y3) /\ ((~ (y4 = y5)) /\ ((y2 y4) = (y2 y5))))) -> (y1 (y2 y4)) = (@neutral a2 y0))) -> (@iterate a2 a1 y0 (@IMAGE a0 a1 y2 y3) y1) = (@iterate a2 a0 y0 y3 (@o a0 a1 a2 y1 y2))) x0.