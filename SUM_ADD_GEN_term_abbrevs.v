Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term50 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := fun y0 : a0 => real_add (x0 y0) (x1 y0).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0))))) y1)).
Definition term45 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := and (@FINITE a0 (@support a0 real real_add x0 x1)).
Definition term73 (a0 : Type') (x0 : type1627) := (@monoidal real x0) -> forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 (@support a0 real x0 y0 y2)) /\ (@FINITE a0 (@support a0 real x0 y1 y2))) -> (@iterate real a0 x0 y2 (fun y3 : a0 => x0 (y0 y3) (y1 y3))) = (x0 (@iterate real a0 x0 y2 y0) (@iterate real a0 x0 y2 y1)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (@monoidal a1 x0) -> forall y0 : a0 -> a1, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, ((@FINITE a0 (@support a0 a1 x0 y0 y2)) /\ (@FINITE a0 (@support a0 a1 x0 y1 y2))) -> (@iterate a1 a0 x0 y2 (fun y3 : a0 => x0 (y0 y3) (y1 y3))) = (x0 (@iterate a1 a0 x0 y2 y0) (@iterate a1 a0 x0 y2 y1)).
Definition term19 := real_of_num (NUMERAL 0).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : type1400 a1, (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((y0 y3) = (@neutral a1 y1)))) y3)) = (@support a0 a1 y1 y0 x0)) x1.
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (@neutral real real_add)))) y0.
Definition term33 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (real_of_num (NUMERAL 0))))) y0.
Definition term72 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 (@support a0 real real_add y0 y2)) /\ (@FINITE a0 (@support a0 real real_add y1 y2))) -> (@iterate real a0 real_add y2 (fun y3 : a0 => real_add (y0 y3) (y1 y3))) = (real_add (@iterate real a0 real_add y2 y0) (@iterate real a0 real_add y2 y1)).
Definition term71 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y2) /\ (~ ((y0 y4) = (real_of_num (NUMERAL 0))))) y4))) /\ (@FINITE a0 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y2) /\ (~ ((y1 y4) = (real_of_num (NUMERAL 0))))) y4)))) -> (@sum a0 y2 (fun y3 : a0 => real_add (y0 y3) (y1 y3))) = (real_add (@sum a0 y2 y0) (@sum a0 y2 y1)).
Definition term18 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, forall y2 : type1400 a1, (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y0) /\ (~ ((y1 y4) = (@neutral a1 y2)))) y4)) = (@support a0 a1 y2 y1 y0).
Definition term17 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, forall y2 : type1400 a1, (@support a0 a1 y2 y1 y0) = (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y0) /\ (~ ((y1 y4) = (@neutral a1 y2)))) y4)).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := forall y0 : a0 -> a1, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, ((@FINITE a0 (@support a0 a1 x0 y0 y2)) /\ (@FINITE a0 (@support a0 a1 x0 y1 y2))) -> (@iterate a1 a0 x0 y2 (fun y3 : a0 => x0 (y0 y3) (y1 y3))) = (x0 (@iterate a1 a0 x0 y2 y0) (@iterate a1 a0 x0 y2 y1)).
Definition term23 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := @eq real (x0 x1).
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, forall y2 : type1400 a1, (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y0) /\ (~ ((y1 y4) = (@neutral a1 y2)))) y4)) = (@support a0 a1 y2 y1 y0)) x0.
Definition term43 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := @FINITE a0 (@support a0 real real_add x0 x1).
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : type1400 a1, (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, ((@FINITE a0 (@support a0 a1 y0 y1 y3)) /\ (@FINITE a0 (@support a0 a1 y0 y2 y3))) -> (@iterate a1 a0 y0 y3 (fun y4 : a0 => y0 (y1 y4) (y2 y4))) = (y0 (@iterate a1 a0 y0 y3 y1) (@iterate a1 a0 y0 y3 y2)).
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ ((x2 x3) = (@neutral real real_add)))) x3.
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))) x3.
Definition term74 (a0 : Type') := (@monoidal real real_add) -> forall y0 : a0 -> real, forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 (@support a0 real real_add y0 y2)) /\ (@FINITE a0 (@support a0 real real_add y1 y2))) -> (@iterate real a0 real_add y2 (fun y3 : a0 => real_add (y0 y3) (y1 y3))) = (real_add (@iterate real a0 real_add y2 y0) (@iterate real a0 real_add y2 y1)).
Definition term64 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, ((@FINITE a0 (@support a0 real real_add x0 y0)) /\ (@FINITE a0 (@support a0 real real_add x1 y0))) -> (@iterate real a0 real_add y0 (fun y1 : a0 => real_add (x0 y1) (x1 y1))) = (real_add (@iterate real a0 real_add y0 x0) (@iterate real a0 real_add y0 x1)).
Definition term63 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, ((@FINITE a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 y0) /\ (~ ((x0 y2) = (real_of_num (NUMERAL 0))))) y2))) /\ (@FINITE a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 y0) /\ (~ ((x1 y2) = (real_of_num (NUMERAL 0))))) y2)))) -> (@sum a0 y0 (fun y1 : a0 => real_add (x0 y1) (x1 y1))) = (real_add (@sum a0 y0 x0) (@sum a0 y0 x1)).
Definition term58 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_add (@iterate real a0 real_add x1 x0) (@iterate real a0 real_add x1 x2).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := forall y0 : type1400 a1, (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ (~ ((x0 y2) = (@neutral a1 y0)))) y2)) = (@support a0 a1 y0 x0 x1).
Definition term59 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x0 y1) = (real_of_num (NUMERAL 0))))) y1))) /\ (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x2 y1) = (real_of_num (NUMERAL 0))))) y1)))) -> (@sum a0 x1 (fun y0 : a0 => real_add (x0 y0) (x2 y0))) = (real_add (@sum a0 x1 x0) (@sum a0 x1 x2)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (forall y0 : type1400 a1, (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, ((@FINITE a0 (@support a0 a1 y0 y1 y3)) /\ (@FINITE a0 (@support a0 a1 y0 y2 y3))) -> (@iterate a1 a0 y0 y3 (fun y4 : a0 => y0 (y1 y4) (y2 y4))) = (y0 (@iterate a1 a0 y0 y3 y1) (@iterate a1 a0 y0 y3 y2))) -> forall y0 : a0 -> a1, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, ((@FINITE a0 (@support a0 a1 x0 y0 y2)) /\ (@FINITE a0 (@support a0 a1 x0 y1 y2))) -> (@iterate a1 a0 x0 y2 (fun y3 : a0 => x0 (y0 y3) (y1 y3))) = (x0 (@iterate a1 a0 x0 y2 y0) (@iterate a1 a0 x0 y2 y1)).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (@IN a0 x2 x0) /\ (~ ((x1 x2) = (@neutral real real_add))).
Definition term24 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := ~ ((x0 x1) = (real_of_num (NUMERAL 0))).
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_add (@sum a0 x0 x1).
Definition term66 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> real => forall y1 : a0 -> Prop, ((@FINITE a0 (@support a0 real real_add x0 y1)) /\ (@FINITE a0 (@support a0 real real_add y0 y1))) -> (@iterate real a0 real_add y1 (fun y2 : a0 => real_add (x0 y2) (y0 y2))) = (real_add (@iterate real a0 real_add y1 x0) (@iterate real a0 real_add y1 y0)).
Definition term65 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> real => forall y1 : a0 -> Prop, ((@FINITE a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y1) /\ (~ ((x0 y3) = (real_of_num (NUMERAL 0))))) y3))) /\ (@FINITE a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y1) /\ (~ ((y0 y3) = (real_of_num (NUMERAL 0))))) y3)))) -> (@sum a0 y1 (fun y2 : a0 => real_add (x0 y2) (y0 y2))) = (real_add (@sum a0 y1 x0) (@sum a0 y1 y0)).
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ ((x2 x3) = (real_of_num (NUMERAL 0))))).
Definition term60 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 (@support a0 real real_add x0 x1)) /\ (@FINITE a0 (@support a0 real real_add x2 x1))) -> (@iterate real a0 real_add x1 (fun y0 : a0 => real_add (x0 y0) (x2 y0))) = (real_add (@iterate real a0 real_add x1 x0) (@iterate real a0 real_add x1 x2)).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := @eq real (@sum a0 x0 (fun y0 : a0 => real_add (x1 y0) (x2 y0))).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : type1627) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (@neutral real x2)))) y1).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (@neutral real real_add)))) y1).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0))))) y1).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (@neutral a1 x2)))) y1).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_add (@iterate real a0 real_add x0 x1).
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (~ ((x2 x3) = (@neutral real real_add)))).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := @iterate real a0 real_add x0 (fun y0 : a0 => real_add (x1 y0) (x2 y0)).
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (@neutral real real_add)))) y0.
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> real) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (~ ((x2 y0) = (real_of_num (NUMERAL 0))))) y0.
Definition term62 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := fun y0 : a0 -> Prop => ((@FINITE a0 (@support a0 real real_add x0 y0)) /\ (@FINITE a0 (@support a0 real real_add x1 y0))) -> (@iterate real a0 real_add y0 (fun y1 : a0 => real_add (x0 y1) (x1 y1))) = (real_add (@iterate real a0 real_add y0 x0) (@iterate real a0 real_add y0 x1)).
Definition term61 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := fun y0 : a0 -> Prop => ((@FINITE a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 y0) /\ (~ ((x0 y2) = (real_of_num (NUMERAL 0))))) y2))) /\ (@FINITE a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 y0) /\ (~ ((x1 y2) = (real_of_num (NUMERAL 0))))) y2)))) -> (@sum a0 y0 (fun y1 : a0 => real_add (x0 y1) (x1 y1))) = (real_add (@sum a0 y0 x0) (@sum a0 y0 x1)).
Definition term46 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x0 y1) = (real_of_num (NUMERAL 0))))) y1))) /\ (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x2 y1) = (real_of_num (NUMERAL 0))))) y1))).
Definition term47 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0 -> Prop) := (@FINITE a0 (@support a0 real real_add x0 x2)) /\ (@FINITE a0 (@support a0 real real_add x1 x2)).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (@IN a0 x2 x0) /\ (~ ((x1 x2) = (real_of_num (NUMERAL 0)))).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := fun y0 : type1400 a1 => (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ (~ ((x0 y2) = (@neutral a1 y0)))) y2)) = (@support a0 a1 y0 x0 x1).
Definition term70 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 (@support a0 real real_add y0 y2)) /\ (@FINITE a0 (@support a0 real real_add y1 y2))) -> (@iterate real a0 real_add y2 (fun y3 : a0 => real_add (y0 y3) (y1 y3))) = (real_add (@iterate real a0 real_add y2 y0) (@iterate real a0 real_add y2 y1)).
Definition term69 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y2) /\ (~ ((y0 y4) = (real_of_num (NUMERAL 0))))) y4))) /\ (@FINITE a0 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y2) /\ (~ ((y1 y4) = (real_of_num (NUMERAL 0))))) y4)))) -> (@sum a0 y2 (fun y3 : a0 => real_add (y0 y3) (y1 y3))) = (real_add (@sum a0 y2 y0) (@sum a0 y2 y1)).
Definition term49 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0 -> Prop) := imp ((@FINITE a0 (@support a0 real real_add x0 x2)) /\ (@FINITE a0 (@support a0 real real_add x1 x2))).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (@neutral real real_add)))) y1.
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0))))) y1.
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := @eq real (@iterate real a0 real_add x0 (fun y0 : a0 => real_add (x1 y0) (x2 y0))).
Definition term68 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, ((@FINITE a0 (@support a0 real real_add x0 y1)) /\ (@FINITE a0 (@support a0 real real_add y0 y1))) -> (@iterate real a0 real_add y1 (fun y2 : a0 => real_add (x0 y2) (y0 y2))) = (real_add (@iterate real a0 real_add y1 x0) (@iterate real a0 real_add y1 y0)).
Definition term67 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, ((@FINITE a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y1) /\ (~ ((x0 y3) = (real_of_num (NUMERAL 0))))) y3))) /\ (@FINITE a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y1) /\ (~ ((y0 y3) = (real_of_num (NUMERAL 0))))) y3)))) -> (@sum a0 y1 (fun y2 : a0 => real_add (x0 y2) (y0 y2))) = (real_add (@sum a0 y1 x0) (@sum a0 y1 y0)).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, forall y1 : type1400 a1, (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((y0 y3) = (@neutral a1 y1)))) y3)) = (@support a0 a1 y1 y0 x0).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> a1, forall y1 : type1400 a1, (@support a0 a1 y1 y0 x0) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((y0 y3) = (@neutral a1 y1)))) y3)).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : type1400 a1, (@support a0 a1 y0 x1 x0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = (@neutral a1 y0)))) y2)).
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : type1400 a1) := (fun y0 : type1400 a1 => (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ (~ ((x0 y2) = (@neutral a1 y0)))) y2)) = (@support a0 a1 y0 x0 x1)) x2.
Definition term25 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := ~ ((x0 x1) = (@neutral real real_add)).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> a1 => forall y1 : type1400 a1, (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((y0 y3) = (@neutral a1 y1)))) y3)) = (@support a0 a1 y1 y0 x0).
Definition term48 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := imp ((@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x0 y1) = (real_of_num (NUMERAL 0))))) y1))) /\ (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (~ ((x2 y1) = (real_of_num (NUMERAL 0))))) y1)))).
Definition term57 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_add (@sum a0 x1 x0) (@sum a0 x1 x2).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (fun y0 : type1400 a1 => (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, ((@FINITE a0 (@support a0 a1 y0 y1 y3)) /\ (@FINITE a0 (@support a0 a1 y0 y2 y3))) -> (@iterate a1 a0 y0 y3 (fun y4 : a0 => y0 (y1 y4) (y2 y4))) = (y0 (@iterate a1 a0 y0 y3 y1) (@iterate a1 a0 y0 y3 y2))) x0.
Definition term16 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> a1, forall y2 : type1400 a1, (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y0) /\ (~ ((y1 y4) = (@neutral a1 y2)))) y4)) = (@support a0 a1 y2 y1 y0).
Definition term15 (a0 : Type') (a1 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> a1, forall y2 : type1400 a1, (@support a0 a1 y2 y1 y0) = (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y0) /\ (~ ((y1 y4) = (@neutral a1 y2)))) y4)).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => real_add (x1 y0) (x2 y0)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := fun y0 : type1400 a1 => (@support a0 a1 y0 x1 x0) = (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (~ ((x1 y2) = (@neutral a1 y0)))) y2)).
Definition term5 (a0 : Type') (a1 : Type') := (forall y0 : type1400 a1, (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, ((@FINITE a0 (@support a0 a1 y0 y1 y3)) /\ (@FINITE a0 (@support a0 a1 y0 y2 y3))) -> (@iterate a1 a0 y0 y3 (fun y4 : a0 => y0 (y1 y4) (y2 y4))) = (y0 (@iterate a1 a0 y0 y3 y1) (@iterate a1 a0 y0 y3 y2))) -> forall y0 : type1400 a1, (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, ((@FINITE a0 (@support a0 a1 y0 y1 y3)) /\ (@FINITE a0 (@support a0 a1 y0 y2 y3))) -> (@iterate a1 a0 y0 y3 (fun y4 : a0 => y0 (y1 y4) (y2 y4))) = (y0 (@iterate a1 a0 y0 y3 y1) (@iterate a1 a0 y0 y3 y2)).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := and (@FINITE a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0))))) y1))).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> a1 => forall y1 : type1400 a1, (@support a0 a1 y1 y0 x0) = (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (~ ((y0 y3) = (@neutral a1 y1)))) y3)).