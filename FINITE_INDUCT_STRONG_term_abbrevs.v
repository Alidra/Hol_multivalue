Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term28 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@FINITE a0 x1) /\ (x0 x1).
Definition term59 (a0 : Type') (x0 : type686 a0) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (x0 y0)) (@EMPTY a0).
Definition term71 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (x0 y0)) -> (@FINITE a0 (@INSERT a0 x1 y0)) /\ (x0 (@INSERT a0 x1 y0)).
Definition term49 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (~ (~ (@FINITE a0 x1))) -> x0 x1.
Definition term56 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => (~ ((forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@FINITE a0 y1) /\ (y0 y1)) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1)) -> False) x0.
Definition term167 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, ((x0 y0) /\ ((~ (@IN a0 x1 y0)) /\ (@FINITE a0 y0))) -> x0 (@INSERT a0 x1 y0).
Definition term111 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (x0 y0)) -> x0 (@INSERT a0 x1 y0).
Definition term159 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term64 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := imp ((fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (x0 y0)) x1).
Definition term55 := (~ False) -> False.
Definition term125 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@INSERT a0 x1 x2)).
Definition term172 (a0 : Type') (x0 : type686 a0) := (forall y0 : a0, forall y1 : a0 -> Prop, ((x0 y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> x0 (@INSERT a0 y0 y1)) -> forall y0 : a0, forall y1 : a0 -> Prop, ((x0 y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> x0 (@INSERT a0 y0 y1).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term0 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : Prop => y0 \/ (~ y0)) (@IN a0 x0 x1).
Definition term21 (x0 : Prop) := ~ (~ x0).
Definition term170 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (x0 x2) /\ ((~ (@IN a0 x1 x2)) /\ (@FINITE a0 x2)).
Definition term26 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> x0 x1.
Definition term124 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x2 = x0) \/ (x1 x2).
Definition term122 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term79 (a0 : Type') (x0 : type686 a0) := ((@FINITE a0 (@EMPTY a0)) /\ (x0 (@EMPTY a0))) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (x0 y1)) -> (@FINITE a0 (@INSERT a0 y0 y1)) /\ (x0 (@INSERT a0 y0 y1))).
Definition term157 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term40 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, ((~ (@FINITE a0 y0)) \/ (@FINITE a0 y0)) /\ ((~ (@FINITE a0 y0)) \/ (x0 y0)).
Definition term121 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term118 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> (@INSERT a0 x0 x1) = x1.
Definition term13 (x0 : Prop) := (~ x0) -> False.
Definition term61 (a0 : Type') (x0 : type686 a0) := and ((fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (x0 y0)) (@EMPTY a0)).
Definition term161 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (~ (x0 x1)).
Definition term137 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (~ ((x0 y0) -> forall y1 : a0, ((y1 = y0) \/ (x0 y1)) = (x0 y1))) -> False.
Definition term140 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> forall y1 : a0, ((y1 = y0) \/ (x0 y1)) = (x0 y1).
Definition term128 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => ((y0 = x0) \/ (x1 y0)) = (x1 y0).
Definition term48 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term58 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (x0 y0).
Definition term102 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : Prop) := (((@FINITE a0 x2) /\ (x1 x2)) -> ((@FINITE a0 (@INSERT a0 x0 x2)) /\ (x1 (@INSERT a0 x0 x2))) = x3) -> (((@FINITE a0 x2) /\ (x1 x2)) -> (@FINITE a0 (@INSERT a0 x0 x2)) /\ (x1 (@INSERT a0 x0 x2))) = (((@FINITE a0 x2) /\ (x1 x2)) -> x3).
Definition term27 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> x0 y0.
Definition term152 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((~ (x2 = x0)) /\ (~ (x1 x2))) /\ (x1 x2).
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term45 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (x0 x1) \/ (~ (@FINITE a0 x1)).
Definition term44 (x0 : Prop) := (~ x0) -> x0.
Definition term74 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 => forall y1 : a0 -> Prop, ((fun y2 : a0 -> Prop => (@FINITE a0 y2) /\ (x0 y2)) y1) -> (fun y2 : a0 -> Prop => (@FINITE a0 y2) /\ (x0 y2)) (@INSERT a0 y0 y1).
Definition term42 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ (x0 x1).
Definition term106 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := True /\ (x0 (@INSERT a0 x1 x2)).
Definition term70 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => (@FINITE a0 y1) /\ (x0 y1)) y0) -> (fun y1 : a0 -> Prop => (@FINITE a0 y1) /\ (x0 y1)) (@INSERT a0 x1 y0).
Definition term88 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> @FINITE a0 (@INSERT a0 x0 y0).
Definition term112 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (x0 y1)) -> x0 (@INSERT a0 y0 y1).
Definition term41 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((~ (@FINITE a0 y0)) \/ (@FINITE a0 y0)) /\ ((~ (@FINITE a0 y0)) \/ (x0 y0))) x1.
Definition term97 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((@FINITE a0 x2) /\ (x0 x2)) = y0) -> (y0 -> ((@FINITE a0 (@INSERT a0 x1 x2)) /\ (x0 (@INSERT a0 x1 x2))) = y1) -> (((@FINITE a0 x2) /\ (x0 x2)) -> (@FINITE a0 (@INSERT a0 x1 x2)) /\ (x0 (@INSERT a0 x1 x2))) = (y0 -> y1)) x3.
Definition term155 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (((x2 = x0) \/ (x1 x2)) /\ (~ (x1 x2))) \/ (((~ (x2 = x0)) /\ (~ (x1 x2))) /\ (x1 x2)).
Definition term81 (a0 : Type') (x0 : type686 a0) := imp (((@FINITE a0 (@EMPTY a0)) /\ (x0 (@EMPTY a0))) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (x0 y1)) -> (@FINITE a0 (@INSERT a0 y0 y1)) /\ (x0 (@INSERT a0 y0 y1)))).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) := imp (~ (~ (@FINITE a0 x0))).
Definition term158 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term101 (a0 : Type') (x0 : a0) (x1 : type686 a0) (x2 : a0 -> Prop) (x3 : Prop) := (((@FINITE a0 x2) /\ (x1 x2)) = ((@FINITE a0 x2) /\ (x1 x2))) -> (((@FINITE a0 x2) /\ (x1 x2)) -> ((@FINITE a0 (@INSERT a0 x0 x2)) /\ (x1 (@INSERT a0 x0 x2))) = x3) -> (((@FINITE a0 x2) /\ (x1 x2)) -> (@FINITE a0 (@INSERT a0 x0 x2)) /\ (x1 (@INSERT a0 x0 x2))) = (((@FINITE a0 x2) /\ (x1 x2)) -> x3).
Definition term136 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ (x1 y0)) = (x1 y0))).
Definition term130 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (x1 x0) -> forall y0 : a0, ((y0 = x0) \/ (x1 y0)) = (x1 y0).
Definition term53 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (~ (x0 x1)) -> x0 x1.
Definition term139 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (~ ((x0 y0) -> forall y1 : a0, ((y1 = y0) \/ (x0 y1)) = (x0 y1))) -> False.
Definition term169 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := ((x0 x2) /\ ((~ (@IN a0 x1 x2)) /\ (@FINITE a0 x2))) -> x0 (@INSERT a0 x1 x2).
Definition term90 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> @FINITE a0 (@INSERT a0 x0 x1).
Definition term36 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (~ (@FINITE a0 y0)) \/ ((@FINITE a0 y0) /\ (x0 y0)).
Definition term168 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((x0 y0) /\ ((~ (@IN a0 x1 y0)) /\ (@FINITE a0 y0))) -> x0 (@INSERT a0 x1 y0)) x2.
Definition term147 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x2 = x0) \/ (x1 x2)).
Definition term22 (a0 : Type') := fun y0 : type686 a0 => (~ ((forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@FINITE a0 y1) /\ (y0 y1)) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1)) -> False.
Definition term166 (a0 : Type') (x0 : type686 a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, ((x0 y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> x0 (@INSERT a0 y0 y1)) x1.
Definition term93 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term66 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (x0 y0)) (@INSERT a0 x1 x2).
Definition term57 (a0 : Type') (x0 : type686 a0) := (((fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (x0 y0)) (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((fun y2 : a0 -> Prop => (@FINITE a0 y2) /\ (x0 y2)) y1) -> (fun y2 : a0 -> Prop => (@FINITE a0 y2) /\ (x0 y2)) (@INSERT a0 y0 y1))) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (fun y1 : a0 -> Prop => (@FINITE a0 y1) /\ (x0 y1)) y0.
Definition term69 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := ((@FINITE a0 x2) /\ (x0 x2)) -> (@FINITE a0 (@INSERT a0 x1 x2)) /\ (x0 (@INSERT a0 x1 x2)).
Definition term143 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (~ ((y0 y1) -> forall y2 : a0, ((y2 = y1) \/ (y0 y2)) = (y0 y2))) -> False.
Definition term38 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term148 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x2 = x0)) /\ (~ (x1 x2)).
Definition term126 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((x2 = x0) \/ (x1 x2)).
Definition term174 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (x0 x1).
Definition term33 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ ((@FINITE a0 x1) /\ (x0 x1)).
Definition term62 (a0 : Type') (x0 : type686 a0) := and ((@FINITE a0 (@EMPTY a0)) /\ (x0 (@EMPTY a0))).
Definition term133 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ (x1 y0)) = (x1 y0))) -> False) -> (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ (x1 y0)) = (x1 y0))) -> False.
Definition term17 (a0 : Type') (x0 : type686 a0) := ((~ ((forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0)) -> False) -> (~ ((forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0)) -> False.
Definition term92 (a0 : Type') := and (@FINITE a0 (@EMPTY a0)).
Definition term35 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (~ (@FINITE a0 y0)) \/ ((@FINITE a0 y0) /\ (x0 y0)).
Definition term104 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@FINITE a0 (@INSERT a0 x0 x1)).
Definition term145 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (((x2 = x0) \/ (x1 x2)) = (x1 x2))) -> False.
Definition term110 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (x0 y0)) -> x0 (@INSERT a0 x1 y0).
Definition term85 (a0 : Type') (x0 : type686 a0) := (((@FINITE a0 (@EMPTY a0)) /\ (x0 (@EMPTY a0))) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (x0 y1)) -> (@FINITE a0 (@INSERT a0 y0 y1)) /\ (x0 (@INSERT a0 y0 y1)))) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0).
Definition term100 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) (x4 : Prop) := (((@FINITE a0 x2) /\ (x0 x2)) = x3) -> (x3 -> ((@FINITE a0 (@INSERT a0 x1 x2)) /\ (x0 (@INSERT a0 x1 x2))) = x4) -> (((@FINITE a0 x2) /\ (x0 x2)) -> (@FINITE a0 (@INSERT a0 x1 x2)) /\ (x0 (@INSERT a0 x1 x2))) = (x3 -> x4).
Definition term173 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> (@IN a0 x0 x1) = False.
Definition term34 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (x0 x1).
Definition term109 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := ((@FINITE a0 x2) /\ (x0 x2)) -> x0 (@INSERT a0 x1 x2).
Definition term129 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, ((y0 = x0) \/ (x1 y0)) = (x1 y0).
Definition term31 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (~ (x0 x1)) -> False.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) := (~ (@FINITE a0 x0)) -> @FINITE a0 x0.
Definition term160 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term1 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) \/ (~ (@IN a0 x0 x1)).
Definition term67 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (@FINITE a0 (@INSERT a0 x1 x2)) /\ (x0 (@INSERT a0 x1 x2)).
Definition term16 (a0 : Type') (x0 : type686 a0) := ~ ((forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0).
Definition term24 (a0 : Type') := forall y0 : type686 a0, (~ ((forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@FINITE a0 y1) /\ (y0 y1)) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1)) -> False.
Definition term107 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := ((@FINITE a0 x2) /\ (x0 x2)) -> ((@FINITE a0 (@INSERT a0 x1 x2)) /\ (x0 (@INSERT a0 x1 x2))) = (x0 (@INSERT a0 x1 x2)).
Definition term30 (a0 : Type') (x0 : type686 a0) := imp (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0)).
Definition term54 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (x0 x1) -> False.
Definition term91 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @FINITE a0 (@INSERT a0 x0 x1).
Definition term114 (a0 : Type') (x0 : type686 a0) := True /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (x0 y1)) -> x0 (@INSERT a0 y0 y1)).
Definition term177 (a0 : Type') (x0 : type686 a0) := ((x0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((x0 y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> x0 (@INSERT a0 y0 y1))) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term5 (a0 : Type') (x0 : type686 a0) := ((x0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (x0 y1) -> x0 (@INSERT a0 y0 y1))) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term138 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (x0 y0) -> forall y1 : a0, ((y1 = y0) \/ (x0 y1)) = (x0 y1).
Definition term119 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> forall y0 : a0, (@IN a0 y0 (@INSERT a0 x0 x1)) = (@IN a0 y0 x1).
Definition term83 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (fun y1 : a0 -> Prop => (@FINITE a0 y1) /\ (x0 y1)) y0.
Definition term46 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop ((~ (@FINITE a0 x1)) \/ (x0 x1)).
Definition term149 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := and (~ ((x2 = x0) \/ (x1 x2))).
Definition term171 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (forall y0 : a0, forall y1 : a0 -> Prop, ((x0 y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> x0 (@INSERT a0 y0 y1)) -> x0 (@INSERT a0 x1 x2).
Definition term73 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (x0 y0)) -> (@FINITE a0 (@INSERT a0 x1 y0)) /\ (x0 (@INSERT a0 x1 y0)).
Definition term98 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := forall y0 : Prop, (((@FINITE a0 x2) /\ (x0 x2)) = x3) -> (x3 -> ((@FINITE a0 (@INSERT a0 x1 x2)) /\ (x0 (@INSERT a0 x1 x2))) = y0) -> (((@FINITE a0 x2) /\ (x0 x2)) -> (@FINITE a0 (@INSERT a0 x1 x2)) /\ (x0 (@INSERT a0 x1 x2))) = (x3 -> y0).
Definition term94 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term39 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => ((~ (@FINITE a0 y0)) \/ (@FINITE a0 y0)) /\ ((~ (@FINITE a0 y0)) \/ (x0 y0)).
Definition term89 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> @FINITE a0 (@INSERT a0 x0 y0)) x1.
Definition term134 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (((~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ (x1 y0)) = (x1 y0))) -> False) -> (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ (x1 y0)) = (x1 y0))) -> False) -> (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ (x1 y0)) = (x1 y0))) -> False.
Definition term18 (a0 : Type') (x0 : type686 a0) := (((~ ((forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0)) -> False) -> (~ ((forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0)) -> False) -> (~ ((forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0)) -> False.
Definition term150 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := and ((~ (x2 = x0)) /\ (~ (x1 x2))).
Definition term96 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := forall y0 : Prop, forall y1 : Prop, (((@FINITE a0 x2) /\ (x0 x2)) = y0) -> (y0 -> ((@FINITE a0 (@INSERT a0 x1 x2)) /\ (x0 (@INSERT a0 x1 x2))) = y1) -> (((@FINITE a0 x2) /\ (x0 x2)) -> (@FINITE a0 (@INSERT a0 x1 x2)) /\ (x0 (@INSERT a0 x1 x2))) = (y0 -> y1).
Definition term95 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term117 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term123 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term178 (a0 : Type') := forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1.
Definition term3 (a0 : Type') := forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (y0 y2) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1.
Definition term20 (a0 : Type') (x0 : type686 a0) := ~ (~ ((forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0)).
Definition term127 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@INSERT a0 x0 x1)) = (@IN a0 y0 x1).
Definition term65 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := imp ((@FINITE a0 x1) /\ (x0 x1)).
Definition term99 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => (((@FINITE a0 x2) /\ (x0 x2)) = x3) -> (x3 -> ((@FINITE a0 (@INSERT a0 x1 x2)) /\ (x0 (@INSERT a0 x1 x2))) = y0) -> (((@FINITE a0 x2) /\ (x0 x2)) -> (@FINITE a0 (@INSERT a0 x1 x2)) /\ (x0 (@INSERT a0 x1 x2))) = (x3 -> y0)) x4.
Definition term37 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ((~ (@FINITE a0 x1)) \/ (@FINITE a0 x1)) /\ ((~ (@FINITE a0 x1)) \/ (x0 x1)).
Definition term146 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ (((x2 = x0) \/ (x1 x2)) = (x1 x2)).
Definition term120 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term103 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@FINITE a0 (@INSERT a0 x0 x1)) = True.
Definition term4 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (y0 y2) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) x0.
Definition term164 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (~ ((y0 y1) -> forall y2 : a0, ((y2 = y1) \/ (y0 y2)) = (y0 y2))) -> False) x0.
Definition term153 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := or (((x2 = x0) \/ (x1 x2)) /\ (~ (x1 x2))).
Definition term165 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (~ ((x0 y0) -> forall y1 : a0, ((y1 = y0) \/ (x0 y1)) = (x0 y1))) -> False) x1.
Definition term12 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0).
Definition term7 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term87 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1)) x0.
Definition term108 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (((@FINITE a0 x2) /\ (x0 x2)) -> ((@FINITE a0 (@INSERT a0 x1 x2)) /\ (x0 (@INSERT a0 x1 x2))) = (x0 (@INSERT a0 x1 x2))) -> (((@FINITE a0 x2) /\ (x0 x2)) -> (@FINITE a0 (@INSERT a0 x1 x2)) /\ (x0 (@INSERT a0 x1 x2))) = (((@FINITE a0 x2) /\ (x0 x2)) -> x0 (@INSERT a0 x1 x2)).
Definition term14 (a0 : Type') (x0 : type686 a0) := (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term8 (a0 : Type') (x0 : type686 a0) := (forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (y0 y2) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term50 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ (@FINITE a0 x0)).
Definition term163 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term63 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (x0 y0)) x1.
Definition term141 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, (~ ((y0 y1) -> forall y2 : a0, ((y2 = y1) \/ (y0 y2)) = (y0 y2))) -> False.
Definition term142 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, (y0 y1) -> forall y2 : a0, ((y2 = y1) \/ (y0 y2)) = (y0 y2).
Definition term154 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (((x2 = x0) \/ (x1 x2)) /\ (~ (x1 x2))) \/ ((~ ((x2 = x0) \/ (x1 x2))) /\ (x1 x2)).
Definition term23 (a0 : Type') := fun y0 : type686 a0 => (forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@FINITE a0 y1) /\ (y0 y1)) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1.
Definition term151 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x2 = x0) \/ (x1 x2))) /\ (x1 x2).
Definition term25 (a0 : Type') := forall y0 : type686 a0, (forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@FINITE a0 y1) /\ (y0 y1)) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1.
Definition term68 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := ((fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (x0 y0)) x2) -> (fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (x0 y0)) (@INSERT a0 x1 x2).
Definition term156 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((x2 = x0) \/ (x1 x2)) /\ (~ (x1 x2)).
Definition term175 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (~ (@IN a0 x0 x1)).
Definition term60 (a0 : Type') (x0 : type686 a0) := (@FINITE a0 (@EMPTY a0)) /\ (x0 (@EMPTY a0)).
Definition term135 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (((~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ (x1 y0)) = (x1 y0))) -> False) -> (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ (x1 y0)) = (x1 y0))) -> False) -> ((~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ (x1 y0)) = (x1 y0))) -> False) -> (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ (x1 y0)) = (x1 y0))) -> False.
Definition term19 (a0 : Type') (x0 : type686 a0) := (((~ ((forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0)) -> False) -> (~ ((forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0)) -> False) -> ((~ ((forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0)) -> False) -> (~ ((forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0)) -> False.
Definition term116 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INSERT a0 x0 x1)) = (@IN a0 y0 x1).
Definition term32 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (x0 x1).
Definition term9 (a0 : Type') := (forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (y0 y2) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) -> forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (y0 y2) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1.
Definition term131 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ (x1 y0)) = (x1 y0))) -> False.
Definition term15 (a0 : Type') (x0 : type686 a0) := (~ ((forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0)) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0)) -> False.
Definition term132 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ ((x1 x0) -> forall y0 : a0, ((y0 = x0) \/ (x1 y0)) = (x1 y0)).
Definition term75 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (x0 y1)) -> (@FINITE a0 (@INSERT a0 y0 y1)) /\ (x0 (@INSERT a0 y0 y1)).
Definition term176 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1).
Definition term10 (a0 : Type') (x0 : type686 a0) := (x0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((x0 y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> x0 (@INSERT a0 y0 y1)).
Definition term6 (a0 : Type') (x0 : type686 a0) := (x0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (x0 y1) -> x0 (@INSERT a0 y0 y1)).
Definition term113 (a0 : Type') (x0 : type686 a0) := forall y0 : a0, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (x0 y1)) -> x0 (@INSERT a0 y0 y1).
Definition term86 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a0 (@INSERT a0 y0 y1).
Definition term77 (a0 : Type') (x0 : type686 a0) := forall y0 : a0, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (x0 y1)) -> (@FINITE a0 (@INSERT a0 y0 y1)) /\ (x0 (@INSERT a0 y0 y1)).
Definition term76 (a0 : Type') (x0 : type686 a0) := forall y0 : a0, forall y1 : a0 -> Prop, ((fun y2 : a0 -> Prop => (@FINITE a0 y2) /\ (x0 y2)) y1) -> (fun y2 : a0 -> Prop => (@FINITE a0 y2) /\ (x0 y2)) (@INSERT a0 y0 y1).
Definition term11 (a0 : Type') (x0 : type686 a0) := forall y0 : a0, forall y1 : a0 -> Prop, ((x0 y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> x0 (@INSERT a0 y0 y1).
Definition term162 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term29 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@FINITE a0 y0) /\ (x0 y0).
Definition term80 (a0 : Type') (x0 : type686 a0) := imp (((fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (x0 y0)) (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((fun y2 : a0 -> Prop => (@FINITE a0 y2) /\ (x0 y2)) y1) -> (fun y2 : a0 -> Prop => (@FINITE a0 y2) /\ (x0 y2)) (@INSERT a0 y0 y1))).
Definition term72 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (@FINITE a0 y1) /\ (x0 y1)) y0) -> (fun y1 : a0 -> Prop => (@FINITE a0 y1) /\ (x0 y1)) (@INSERT a0 x1 y0).
Definition term144 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (y0 y1) -> forall y2 : a0, ((y2 = y1) \/ (y0 y2)) = (y0 y2).
Definition term84 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (fun y1 : a0 -> Prop => (@FINITE a0 y1) /\ (x0 y1)) y0.
Definition term105 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := x0 (@INSERT a0 x1 x2).
Definition term47 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @eq Prop ((x0 x1) \/ (~ (@FINITE a0 x1))).
Definition term78 (a0 : Type') (x0 : type686 a0) := ((fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (x0 y0)) (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((fun y2 : a0 -> Prop => (@FINITE a0 y2) /\ (x0 y2)) y1) -> (fun y2 : a0 -> Prop => (@FINITE a0 y2) /\ (x0 y2)) (@INSERT a0 y0 y1)).
Definition term82 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (x0 y0)) x1.