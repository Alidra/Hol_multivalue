Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : Prop) := ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) = (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add))) -> ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) -> ((@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = x2) -> ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) -> (@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) -> x2).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := (@monoidal a1 x2) -> (@iterate a1 a0 x2 x0 x1) = (@neutral a1 x2).
Definition term58 (a0 : Type') (x0 : a0 -> real) (x1 : a0) (x2 : a0 -> Prop) := ((@IN a0 x1 x2) -> ((x0 x1) = (@neutral real real_add)) = True) -> ((@IN a0 x1 x2) -> (x0 x1) = (@neutral real real_add)) = ((@IN a0 x1 x2) -> True).
Definition term10 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (@monoidal a1 x0) -> forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (y0 y2) = (@neutral a1 x0)) -> (@iterate a1 a0 x0 y1 y0) = (@neutral a1 x0).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (real_of_num (NUMERAL 0))) -> (@sum a0 x0 x1) = (real_of_num (NUMERAL 0)).
Definition term13 := real_of_num (NUMERAL 0).
Definition term30 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (real_of_num (NUMERAL 0))) -> (@sum a0 y0 x0) = (real_of_num (NUMERAL 0)).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (y0 y2) = (@neutral a1 x0)) -> (@iterate a1 a0 x0 y1 y0) = (@neutral a1 x0)) x1.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (@neutral a1 x1)) -> (@iterate a1 a0 x1 y0 x0) = (@neutral a1 x1)) x2.
Definition term62 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term54 (a0 : Type') (x0 : a0 -> real) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := ((@IN a0 x1 x2) = (@IN a0 x1 x2)) -> ((@IN a0 x1 x2) -> ((x0 x1) = (@neutral real real_add)) = x3) -> ((@IN a0 x1 x2) -> (x0 x1) = (@neutral real real_add)) = ((@IN a0 x1 x2) -> x3).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (@IN a0 x2 x0) -> (x1 x2) = (real_of_num (NUMERAL 0)).
Definition term14 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := @eq real (x0 x1).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := imp (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := imp (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (real_of_num (NUMERAL 0))).
Definition term61 (a0 : Type') := forall y0 : a0, True.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (@neutral a1 x1)) -> (@iterate a1 a0 x1 y0 x0) = (@neutral a1 x1).
Definition term59 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> True.
Definition term73 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> real, x0.
Definition term70 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := and (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) -> True.
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN a0 x2 x0) = y0) -> (y0 -> ((x1 x2) = (@neutral real real_add)) = y1) -> ((@IN a0 x2 x0) -> (x1 x2) = (@neutral real real_add)) = (y0 -> y1)) x3.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral a1 x2).
Definition term31 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (@neutral real real_add)) -> (@iterate real a0 real_add y0 x0) = (@neutral real real_add).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := fun y0 : a0 => (@IN a0 y0 x0) -> (x1 y0) = (real_of_num (NUMERAL 0)).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (@IN a0 x2 x0) -> ((x1 x2) = (@neutral real real_add)) = True.
Definition term36 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : Prop) (x4 : Prop) := ((@IN a0 x2 x0) = x3) -> (x3 -> ((x1 x2) = (@neutral real real_add)) = x4) -> ((@IN a0 x2 x0) -> (x1 x2) = (@neutral real real_add)) = (x3 -> x4).
Definition term33 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (y0 y2) = (@neutral real real_add)) -> (@iterate real a0 real_add y1 y0) = (@neutral real real_add).
Definition term32 (a0 : Type') := fun y0 : a0 -> real => forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (y0 y2) = (real_of_num (NUMERAL 0))) -> (@sum a0 y1 y0) = (real_of_num (NUMERAL 0)).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (@IN a0 x2 x0) -> (x1 x2) = (@neutral real real_add).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) /\ (@monoidal real real_add).
Definition term28 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (real_of_num (NUMERAL 0))) -> (@sum a0 y0 x0) = (real_of_num (NUMERAL 0)).
Definition term60 (a0 : Type') := fun y0 : a0 => True.
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((forall y1 : a0, (@IN a0 y1 x0) -> (x1 y1) = (@neutral real real_add)) = x2) -> (x2 -> ((@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = y0) -> ((forall y1 : a0, (@IN a0 y1 x0) -> (x1 y1) = (@neutral real real_add)) -> (@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = (x2 -> y0)) x3.
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq real (@sum a0 x0 x1).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) -> ((@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = True.
Definition term29 (a0 : Type') (x0 : a0 -> real) := fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (@neutral real real_add)) -> (@iterate real a0 real_add y0 x0) = (@neutral real real_add).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : Prop) := forall y0 : Prop, ((@IN a0 x2 x0) = x3) -> (x3 -> ((x1 x2) = (@neutral real real_add)) = y0) -> ((@IN a0 x2 x0) -> (x1 x2) = (@neutral real real_add)) = (x3 -> y0).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : Prop) := forall y0 : Prop, ((forall y1 : a0, (@IN a0 y1 x0) -> (x1 y1) = (@neutral real real_add)) = x2) -> (x2 -> ((@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = y0) -> ((forall y1 : a0, (@IN a0 y1 x0) -> (x1 y1) = (@neutral real real_add)) -> (@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = (x2 -> y0).
Definition term37 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term68 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term71 (a0 : Type') := fun y0 : a0 -> real => True.
Definition term56 := @eq real (@neutral real real_add).
Definition term11 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := forall y0 : Prop, forall y1 : Prop, ((@IN a0 x2 x0) = y0) -> (y0 -> ((x1 x2) = (@neutral real real_add)) = y1) -> ((@IN a0 x2 x0) -> (x1 x2) = (@neutral real real_add)) = (y0 -> y1).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := forall y0 : Prop, forall y1 : Prop, ((forall y2 : a0, (@IN a0 y2 x0) -> (x1 y2) = (@neutral real real_add)) = y0) -> (y0 -> ((@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = y1) -> ((forall y2 : a0, (@IN a0 y2 x0) -> (x1 y2) = (@neutral real real_add)) -> (@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = (y0 -> y1).
Definition term38 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) x2.
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term55 (a0 : Type') (x0 : a0 -> real) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := ((@IN a0 x1 x2) -> ((x0 x1) = (@neutral real real_add)) = x3) -> ((@IN a0 x1 x2) -> (x0 x1) = (@neutral real real_add)) = ((@IN a0 x1 x2) -> x3).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral a1 x2)) -> (@monoidal a1 x2) -> (@iterate a1 a0 x2 x0 x1) = (@neutral a1 x2).
Definition term35 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (y0 y2) = (@neutral real real_add)) -> (@iterate real a0 real_add y1 y0) = (@neutral real real_add).
Definition term34 (a0 : Type') := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (y0 y2) = (real_of_num (NUMERAL 0))) -> (@sum a0 y1 y0) = (real_of_num (NUMERAL 0)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (y0 y2) = (@neutral a1 x0)) -> (@iterate a1 a0 x0 y1 y0) = (@neutral a1 x0).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((@IN a0 x2 x0) = x3) -> (x3 -> ((x1 x2) = (@neutral real real_add)) = y0) -> ((@IN a0 x2 x0) -> (x1 x2) = (@neutral real real_add)) = (x3 -> y0)) x4.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add).
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : type1627) := ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real x2)) /\ (@monoidal real x2)) -> (@iterate real a0 x2 x0 x1) = (@neutral real x2).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral a1 x2)) /\ (@monoidal a1 x2)) -> (@iterate a1 a0 x2 x0 x1) = (@neutral a1 x2).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : Prop) := ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) -> ((@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = x2) -> ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) -> (@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) -> x2).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (real_of_num (NUMERAL 0)).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) -> ((@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = True) -> ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) -> (@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) -> True).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := @eq real (@iterate real a0 real_add x0 x1).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (fun y0 : type1400 a1 => (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y1 y3) = (@neutral a1 y0)) -> (@iterate a1 a0 y0 y2 y1) = (@neutral a1 y0)) x0.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral a1 x2)) -> (@iterate a1 a0 x2 x0 x1) = (@neutral a1 x2).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((forall y2 : a0, (@IN a0 y2 x0) -> (x1 y2) = (@neutral real real_add)) = y0) -> (y0 -> ((@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = y1) -> ((forall y2 : a0, (@IN a0 y2 x0) -> (x1 y2) = (@neutral real real_add)) -> (@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = (y0 -> y1)) x2.
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) -> (@iterate real a0 real_add x0 x1) = (@neutral real real_add).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) /\ (@monoidal real real_add)) -> (@iterate real a0 real_add x0 x1) = (@neutral real real_add).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : Prop) (x3 : Prop) := ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) = x2) -> (x2 -> ((@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = x3) -> ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral real real_add)) -> (@iterate real a0 real_add x0 x1) = (@neutral real real_add)) = (x2 -> x3).
Definition term72 (a0 : Type') := forall y0 : a0 -> real, True.
Definition term69 (a0 : Type') := forall y0 : a0 -> Prop, True.
