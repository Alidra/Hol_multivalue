Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0) := @COND real (@IN a0 x2 x0) ((fun y0 : a0 => x1) x2).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := (@monoidal a0 x0) -> forall y0 : a1 -> a0, forall y1 : a1, forall y2 : a1 -> Prop, (@iterate a0 a1 x0 y2 (fun y3 : a1 => @COND a0 (y3 = y1) (y0 y3) (@neutral a0 x0))) = (@COND a0 (@IN a1 y1 y2) (y0 y1) (@neutral a0 x0)).
Definition term10 := real_of_num (NUMERAL 0).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : a1 -> a0) (x3 : type1400 a0) := @iterate a0 a1 x3 x0 (fun y0 : a1 => @COND a0 (y0 = x1) (x2 y0) (@neutral a0 x3)).
Definition term50 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term49 (a0 : Type') := forall y0 : a0, True.
Definition term39 (a0 : Type') (x0 : a0) (x1 : real) := fun y0 : a0 => @COND real (y0 = x0) ((fun y1 : a0 => x1) y0) (@neutral real real_add).
Definition term15 (a0 : Type') (x0 : a0) (x1 : real) := fun y0 : a0 => @COND real (y0 = x0) x1 (@neutral real real_add).
Definition term53 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term35 (a0 : Type') (x0 : real) (x1 : a0) := (fun y0 : a0 => x0) x1.
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0) := @COND real (x0 = x1).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) (x3 : type1400 a0) := @COND a0 (@IN a1 x2 x0) (x1 x2) (@neutral a0 x3).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0) := (@monoidal real real_add) -> (@iterate real a0 real_add x0 (fun y0 : a0 => @COND real (y0 = x2) ((fun y1 : a0 => x1) y0) (@neutral real real_add))) = (@COND real (@IN a0 x2 x0) ((fun y0 : a0 => x1) x2) (@neutral real real_add)).
Definition term38 (a0 : Type') (x0 : a0) (x1 : real) (x2 : a0) := @COND real (x2 = x0) ((fun y0 : a0 => x1) x2) (@neutral real real_add).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : type1400 a0) (x2 : a1) := (fun y0 : a1 => forall y1 : a1 -> Prop, (@iterate a0 a1 x1 y1 (fun y2 : a1 => @COND a0 (y2 = y0) (x0 y2) (@neutral a0 x1))) = (@COND a0 (@IN a1 y0 y1) (x0 y0) (@neutral a0 x1))) x2.
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : type1627) := (@monoidal real x3) -> (@iterate real a0 x3 x0 (fun y0 : a0 => @COND real (y0 = x2) (x1 y0) (@neutral real x3))) = (@COND real (@IN a0 x2 x0) (x1 x2) (@neutral real x3)).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) (x3 : type1400 a0) := (@monoidal a0 x3) -> (@iterate a0 a1 x3 x0 (fun y0 : a1 => @COND a0 (y0 = x2) (x1 y0) (@neutral a0 x3))) = (@COND a0 (@IN a1 x2 x0) (x1 x2) (@neutral a0 x3)).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) := forall y0 : a0, (@iterate real a0 real_add x0 (fun y1 : a0 => @COND real (y1 = y0) x1 (@neutral real real_add))) = (@COND real (@IN a0 y0 x0) x1 (@neutral real real_add)).
Definition term45 := imp (@monoidal real real_add).
Definition term14 (a0 : Type') (x0 : a0) (x1 : real) := fun y0 : a0 => @COND real (y0 = x0) x1 (real_of_num (NUMERAL 0)).
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : real) := @eq real (@COND real (@IN a0 x0 x1) x2 (@neutral real real_add)).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : real) := @eq real (@sum a0 x0 (fun y0 : a0 => @COND real (y0 = x1) x2 (real_of_num (NUMERAL 0)))).
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : real) := @COND real (@IN a0 x0 x1) x2 (real_of_num (NUMERAL 0)).
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : real) := @COND real (x0 = x1) x2 (real_of_num (NUMERAL 0)).
Definition term28 (a0 : Type') (x0 : real) := fun y0 : a0 -> Prop => forall y1 : a0, (@iterate real a0 real_add y0 (fun y2 : a0 => @COND real (y2 = y1) x0 (@neutral real real_add))) = (@COND real (@IN a0 y1 y0) x0 (@neutral real real_add)).
Definition term27 (a0 : Type') (x0 : real) := fun y0 : a0 -> Prop => forall y1 : a0, (@sum a0 y0 (fun y2 : a0 => @COND real (y2 = y1) x0 (real_of_num (NUMERAL 0)))) = (@COND real (@IN a0 y1 y0) x0 (real_of_num (NUMERAL 0))).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := (fun y0 : type1400 a0 => (@monoidal a0 y0) -> forall y1 : a1 -> a0, forall y2 : a1, forall y3 : a1 -> Prop, (@iterate a0 a1 y0 y3 (fun y4 : a1 => @COND a0 (y4 = y2) (y1 y4) (@neutral a0 y0))) = (@COND a0 (@IN a1 y2 y3) (y1 y2) (@neutral a0 y0))) x0.
Definition term48 (a0 : Type') := fun y0 : a0 => True.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : type1400 a0) := forall y0 : a1, forall y1 : a1 -> Prop, (@iterate a0 a1 x1 y1 (fun y2 : a1 => @COND a0 (y2 = y0) (x0 y2) (@neutral a0 x1))) = (@COND a0 (@IN a1 y0 y1) (x0 y0) (@neutral a0 x1)).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : real) := @sum a0 x0 (fun y0 : a0 => @COND real (y0 = x1) x2 (real_of_num (NUMERAL 0))).
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : real) := (@monoidal real real_add) -> (@iterate real a0 real_add x1 (fun y0 : a0 => @COND real (y0 = x0) x2 (@neutral real real_add))) = (@COND real (@IN a0 x0 x1) x2 (@neutral real real_add)).
Definition term51 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) (x2 : type1400 a0) := forall y0 : a1 -> Prop, (@iterate a0 a1 x2 y0 (fun y1 : a1 => @COND a0 (y1 = x1) (x0 y1) (@neutral a0 x2))) = (@COND a0 (@IN a1 x1 y0) (x0 x1) (@neutral a0 x2)).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : real) := @eq real (@iterate real a0 real_add x0 (fun y0 : a0 => @COND real (y0 = x1) ((fun y1 : a0 => x2) y0) (@neutral real real_add))).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : real) := @eq real (@iterate real a0 real_add x0 (fun y0 : a0 => @COND real (y0 = x1) x2 (@neutral real real_add))).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) (x2 : type1400 a0) (x3 : a1 -> Prop) := (fun y0 : a1 -> Prop => (@iterate a0 a1 x2 y0 (fun y1 : a1 => @COND a0 (y1 = x1) (x0 y1) (@neutral a0 x2))) = (@COND a0 (@IN a1 x1 y0) (x0 x1) (@neutral a0 x2))) x3.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : real) := @iterate real a0 real_add x0 (fun y0 : a0 => @COND real (y0 = x1) x2 (@neutral real real_add)).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : real) := @COND real (@IN a0 x0 x1) x2.
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1400 a0) (x1 : a1 -> a0) := (fun y0 : a1 -> a0 => forall y1 : a1, forall y2 : a1 -> Prop, (@iterate a0 a1 x0 y2 (fun y3 : a1 => @COND a0 (y3 = y1) (y0 y3) (@neutral a0 x0))) = (@COND a0 (@IN a1 y1 y2) (y0 y1) (@neutral a0 x0))) x1.
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) := fun y0 : a0 => (@sum a0 x0 (fun y1 : a0 => @COND real (y1 = y0) x1 (real_of_num (NUMERAL 0)))) = (@COND real (@IN a0 y0 x0) x1 (real_of_num (NUMERAL 0))).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) (x2 : a0) := @COND real (@IN a0 x2 x0) ((fun y0 : a0 => x1) x2) (@neutral real real_add).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) := forall y0 : a0, (@sum a0 x0 (fun y1 : a0 => @COND real (y1 = y0) x1 (real_of_num (NUMERAL 0)))) = (@COND real (@IN a0 y0 x0) x1 (real_of_num (NUMERAL 0))).
Definition term37 (a0 : Type') (x0 : a0) (x1 : real) (x2 : a0) := @COND real (x2 = x0) ((fun y0 : a0 => x1) x2).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := forall y0 : a1 -> a0, forall y1 : a1, forall y2 : a1 -> Prop, (@iterate a0 a1 x0 y2 (fun y3 : a1 => @COND a0 (y3 = y1) (y0 y3) (@neutral a0 x0))) = (@COND a0 (@IN a1 y1 y2) (y0 y1) (@neutral a0 x0)).
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : real) := @COND real (@IN a0 x0 x1) x2 (@neutral real real_add).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : real) := @COND real (x0 = x1) x2 (@neutral real real_add).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) := fun y0 : a0 => (@iterate real a0 real_add x0 (fun y1 : a0 => @COND real (y1 = y0) x1 (@neutral real real_add))) = (@COND real (@IN a0 y0 x0) x1 (@neutral real real_add)).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : real) := @iterate real a0 real_add x0 (fun y0 : a0 => @COND real (y0 = x1) ((fun y1 : a0 => x2) y0) (@neutral real real_add)).
Definition term34 (a0 : Type') (x0 : real) := fun y0 : a0 => x0.
Definition term30 (a0 : Type') (x0 : real) := forall y0 : a0 -> Prop, forall y1 : a0, (@iterate real a0 real_add y0 (fun y2 : a0 => @COND real (y2 = y1) x0 (@neutral real real_add))) = (@COND real (@IN a0 y1 y0) x0 (@neutral real real_add)).
Definition term29 (a0 : Type') (x0 : real) := forall y0 : a0 -> Prop, forall y1 : a0, (@sum a0 y0 (fun y2 : a0 => @COND real (y2 = y1) x0 (real_of_num (NUMERAL 0)))) = (@COND real (@IN a0 y1 y0) x0 (real_of_num (NUMERAL 0))).
Definition term42 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND real (@IN a0 x0 x1).
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : real) := @COND real (x0 = x1) x2.
Definition term52 (a0 : Type') := forall y0 : a0 -> Prop, True.
