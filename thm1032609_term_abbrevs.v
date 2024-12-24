Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : Prop) := forall y0 : Prop, (y0 -> x0) = ((~ x0) -> ~ y0).
Definition term97 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1400 a0) (x3 : a0) (x4 : type1400 a0) (x5 : a0) (x6 : a0) := ((x0 = x3) /\ (~ (x1 = x6))) -> ~ ((x2 x0 (x4 x5 x1)) = (x2 x3 (x4 x5 x6))).
Definition term40 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) (x2 : a0) (x3 : a0) (x4 : a0) (x5 : a0) := (fun y0 : a0 => ((x0 (x1 x2 x4) (x1 x3 y0)) = (x0 (x1 x2 y0) (x1 x3 x4))) = ((x2 = x3) \/ (x4 = y0))) x5.
Definition term85 (x0 : Prop) := ~ (~ x0).
Definition term89 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1400 a0) (x3 : a0) (x4 : a0) (x5 : type1400 a0) (x6 : a0) (x7 : a0) (x8 : Prop) := (((x5 x6 x4) = (x5 x6 x7)) -> (~ (((x2 (x5 x3 x7) (x5 x6 x4)) = (x2 (x5 x3 x4) (x5 x6 x7))) = ((x3 = x6) \/ (x7 = x4)))) = x8) -> ((~ (~ ((x2 x0 (x5 x6 x4)) = (x2 x1 (x5 x6 x7))))) -> ~ (((x2 (x5 x3 x7) (x5 x6 x4)) = (x2 (x5 x3 x4) (x5 x6 x7))) = ((x3 = x6) \/ (x7 = x4)))) = (((x5 x6 x4) = (x5 x6 x7)) -> x8).
Definition term34 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) (x2 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0, forall y3 : a0, ((x0 (x1 y0 y2) (x1 y1 y3)) = (x0 (x1 y0 y3) (x1 y1 y2))) = ((y0 = y1) \/ (y2 = y3))) x2.
Definition term42 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) := (x0 = x1) \/ (x2 = x3).
Definition term22 (x0 : Prop) := forall y0 : Prop, (((~ x0) \/ (~ y0)) = (~ (x0 /\ y0))) /\ (((~ x0) /\ (~ y0)) = (~ (x0 \/ y0))).
Definition term10 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 -> x0) = ((~ x0) -> ~ y0)) x1.
Definition term52 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term71 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : a0) := (fun y0 : a0 => forall y1 : a0, ((x0 x1 y0) = (x0 x1 y1)) = (y0 = y1)) x2.
Definition term99 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : type1400 a0) (x4 : a0) (x5 : type1400 a0) (x6 : a0) := forall y0 : a0, (~ (x6 = x0)) -> ((x1 = x4) /\ (~ (x2 = y0))) -> ~ ((x3 x1 (x5 x6 x2)) = (x3 x4 (x5 x6 y0))).
Definition term106 (a0 : Type') := forall y0 : type1400 a0, forall y1 : type1400 a0, forall y2 : a0, ((forall y3 : a0, (y1 y2 y3) = y2) /\ ((forall y3 : a0, forall y4 : a0, forall y5 : a0, ((y0 y3 y4) = (y0 y3 y5)) = (y4 = y5)) /\ (forall y3 : a0, forall y4 : a0, forall y5 : a0, forall y6 : a0, ((y0 (y1 y3 y5) (y1 y4 y6)) = (y0 (y1 y3 y6) (y1 y4 y5))) = ((y3 = y4) \/ (y5 = y6))))) -> (forall y3 : a0, forall y4 : a0, forall y5 : a0, forall y6 : a0, ((~ (y3 = y4)) /\ (~ (y5 = y6))) = (~ ((y0 (y1 y3 y5) (y1 y4 y6)) = (y0 (y1 y3 y6) (y1 y4 y5))))) /\ (forall y3 : a0, forall y4 : a0, forall y5 : a0, forall y6 : a0, forall y7 : a0, (~ (y3 = y2)) -> ((y4 = y5) /\ (~ (y6 = y7))) -> ~ ((y0 y4 (y1 y3 y6)) = (y0 y5 (y1 y3 y7)))).
Definition term74 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x0 = x1)) -> (x0 = x1) = False.
Definition term3 (x0 : Prop) := forall y0 : Prop, ((~ x0) -> ~ y0) = (y0 -> x0).
Definition term5 := fun y0 : Prop => forall y1 : Prop, ((~ y0) -> ~ y1) = (y1 -> y0).
Definition term51 (a0 : Type') := forall y0 : a0, True.
Definition term38 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) (x2 : a0) (x3 : a0) (x4 : a0) := (fun y0 : a0 => forall y1 : a0, ((x0 (x1 x2 y0) (x1 x3 y1)) = (x0 (x1 x2 y1) (x1 x3 y0))) = ((x2 = x3) \/ (y0 = y1))) x4.
Definition term43 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) := (~ (x0 = x1)) /\ (~ (x2 = x3)).
Definition term65 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : type1400 a0) (x4 : a0) (x5 : type1400 a0) (x6 : a0) (x7 : a0) := (((x3 (x5 x0 x7) (x5 x6 x2)) = (x3 (x5 x0 x2) (x5 x6 x7))) = ((x0 = x6) \/ (x7 = x2))) -> ~ ((x3 x1 (x5 x6 x2)) = (x3 x4 (x5 x6 x7))).
Definition term66 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1400 a0) (x3 : type1400 a0) (x4 : a0) (x5 : a0) (x6 : a0) (x7 : a0) := (~ (~ ((x2 x0 (x3 x5 x7)) = (x2 x1 (x3 x5 x6))))) -> ~ (((x2 (x3 x4 x6) (x3 x5 x7)) = (x2 (x3 x4 x7) (x3 x5 x6))) = ((x4 = x5) \/ (x6 = x7))).
Definition term98 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : type1400 a0) (x4 : a0) (x5 : type1400 a0) (x6 : a0) (x7 : a0) := (~ (x6 = x0)) -> ((x1 = x4) /\ (~ (x2 = x7))) -> ~ ((x3 x1 (x5 x6 x2)) = (x3 x4 (x5 x6 x7))).
Definition term12 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term68 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (x0 x1 y0) = x1) x2.
Definition term17 (x0 : Prop) (x1 : Prop) := ((~ (x0 /\ x1)) = ((~ x0) \/ (~ x1))) /\ ((~ (x0 \/ x1)) = ((~ x0) /\ (~ x1))).
Definition term83 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1400 a0) (x3 : type1400 a0) (x4 : a0) (x5 : a0) (x6 : a0) (x7 : a0) (x8 : Prop) (x9 : Prop) := (fun y0 : Prop => ((~ (~ ((x2 x0 (x3 x5 x7)) = (x2 x1 (x3 x5 x6))))) = x8) -> (x8 -> (~ (((x2 (x3 x4 x6) (x3 x5 x7)) = (x2 (x3 x4 x7) (x3 x5 x6))) = ((x4 = x5) \/ (x6 = x7)))) = y0) -> ((~ (~ ((x2 x0 (x3 x5 x7)) = (x2 x1 (x3 x5 x6))))) -> ~ (((x2 (x3 x4 x6) (x3 x5 x7)) = (x2 (x3 x4 x7) (x3 x5 x6))) = ((x4 = x5) \/ (x6 = x7)))) = (x8 -> y0)) x9.
Definition term16 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term41 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : a0) (x3 : type1400 a0) (x4 : a0) (x5 : a0) := x0 (x3 x1 x2) (x3 x4 x5).
Definition term84 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1400 a0) (x3 : type1400 a0) (x4 : a0) (x5 : a0) (x6 : a0) (x7 : a0) (x8 : Prop) (x9 : Prop) := ((~ (~ ((x2 x0 (x3 x5 x7)) = (x2 x1 (x3 x5 x6))))) = x8) -> (x8 -> (~ (((x2 (x3 x4 x6) (x3 x5 x7)) = (x2 (x3 x4 x7) (x3 x5 x6))) = ((x4 = x5) \/ (x6 = x7)))) = x9) -> ((~ (~ ((x2 x0 (x3 x5 x7)) = (x2 x1 (x3 x5 x6))))) -> ~ (((x2 (x3 x4 x6) (x3 x5 x7)) = (x2 (x3 x4 x7) (x3 x5 x6))) = ((x4 = x5) \/ (x6 = x7)))) = (x8 -> x9).
Definition term32 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((~ y0) \/ (~ y1)) = (~ (y0 /\ y1))) /\ (((~ y0) /\ (~ y1)) = (~ (y0 \/ y1)))) x0.
Definition term9 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (y1 -> y0) = ((~ y0) -> ~ y1)) x0.
Definition term11 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term94 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) (x2 : a0) (x3 : a0) (x4 : a0) (x5 : a0) := ((x1 x3 x5) = (x1 x3 x4)) -> (~ (((x0 (x1 x2 x4) (x1 x3 x5)) = (x0 (x1 x2 x5) (x1 x3 x4))) = ((x2 = x3) \/ (x4 = x5)))) = True.
Definition term21 (x0 : Prop) := forall y0 : Prop, ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0))).
Definition term48 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : type1400 a0) (x3 : a0) (x4 : a0) := fun y0 : a0 => ((~ (x1 = x3)) /\ (~ (x4 = y0))) = (~ ((x0 (x2 x1 x4) (x2 x3 y0)) = (x0 (x2 x1 y0) (x2 x3 x4)))).
Definition term61 (a0 : Type') (x0 : a0) (x1 : type1400 a0) (x2 : type1400 a0) := (forall y0 : a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((~ (y0 = y1)) /\ (~ (y2 = y3))) = (~ ((x1 (x2 y0 y2) (x2 y1 y3)) = (x1 (x2 y0 y3) (x2 y1 y2))))) /\ (forall y0 : a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, forall y4 : a0, (~ (y0 = x0)) -> ((y1 = y2) /\ (~ (y3 = y4))) -> ~ ((x1 y1 (x2 y0 y3)) = (x1 y2 (x2 y0 y4)))).
Definition term28 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) := (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) = (x0 y0 y2)) = (y1 = y2)) /\ (forall y0 : a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((x0 (x1 y0 y2) (x1 y1 y3)) = (x0 (x1 y0 y3) (x1 y1 y2))) = ((y0 = y1) \/ (y2 = y3))).
Definition term86 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : type1400 a0) (x3 : a0) (x4 : a0) := x0 x1 (x2 x3 x4).
Definition term19 (x0 : Prop) := fun y0 : Prop => ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0))).
Definition term24 := fun y0 : Prop => forall y1 : Prop, (((~ y0) \/ (~ y1)) = (~ (y0 /\ y1))) /\ (((~ y0) /\ (~ y1)) = (~ (y0 \/ y1))).
Definition term23 := fun y0 : Prop => forall y1 : Prop, ((~ (y0 /\ y1)) = ((~ y0) \/ (~ y1))) /\ ((~ (y0 \/ y1)) = ((~ y0) /\ (~ y1))).
Definition term6 := fun y0 : Prop => forall y1 : Prop, (y1 -> y0) = ((~ y0) -> ~ y1).
Definition term80 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) (x2 : a0) (x3 : a0) (x4 : a0) (x5 : a0) := ~ (((x0 (x1 x2 x4) (x1 x3 x5)) = (x0 (x1 x2 x5) (x1 x3 x4))) = ((x2 = x3) \/ (x4 = x5))).
Definition term57 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) := fun y0 : a0 => forall y1 : a0, forall y2 : a0, forall y3 : a0, ((~ (y0 = y1)) /\ (~ (y2 = y3))) = (~ ((x0 (x1 y0 y2) (x1 y1 y3)) = (x0 (x1 y0 y3) (x1 y1 y2)))).
Definition term55 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : type1400 a0) := fun y0 : a0 => forall y1 : a0, forall y2 : a0, ((~ (x1 = y0)) /\ (~ (y1 = y2))) = (~ ((x0 (x2 x1 y1) (x2 y0 y2)) = (x0 (x2 x1 y2) (x2 y0 y1)))).
Definition term0 (x0 : Prop) (x1 : Prop) := (~ x0) -> ~ x1.
Definition term73 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : a0) (x3 : a0) := (fun y0 : a0 => ((x0 x1 x2) = (x0 x1 y0)) = (x2 = y0)) x3.
Definition term75 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term53 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : type1400 a0) (x3 : a0) := fun y0 : a0 => forall y1 : a0, ((~ (x1 = x3)) /\ (~ (y0 = y1))) = (~ ((x0 (x2 x1 y0) (x2 x3 y1)) = (x0 (x2 x1 y1) (x2 x3 y0)))).
Definition term13 (x0 : Prop) (x1 : Prop) := and ((~ (x0 /\ x1)) = ((~ x0) \/ (~ x1))).
Definition term64 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) := (x0 = x1) /\ (~ (x2 = x3)).
Definition term15 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term45 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) := @eq Prop ((~ (x0 = x1)) /\ (~ (x2 = x3))).
Definition term49 (a0 : Type') := fun y0 : a0 => True.
Definition term91 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : a0) (x3 : type1400 a0) (x4 : a0) (x5 : a0) := @eq a0 (x0 (x3 x1 x2) (x3 x4 x5)).
Definition term67 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1400 a0) (x3 : a0) (x4 : type1400 a0) (x5 : a0) (x6 : a0) := ~ ((x2 x0 (x4 x5 x1)) = (x2 x3 (x4 x5 x6))).
Definition term102 (a0 : Type') (x0 : a0) (x1 : type1400 a0) (x2 : type1400 a0) (x3 : a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, (~ (x3 = x0)) -> ((y0 = y1) /\ (~ (y2 = y3))) -> ~ ((x1 y0 (x2 x3 y2)) = (x1 y1 (x2 x3 y3))).
Definition term101 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1400 a0) (x3 : type1400 a0) (x4 : a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, (~ (x4 = x0)) -> ((x1 = y0) /\ (~ (y1 = y2))) -> ~ ((x2 x1 (x3 x4 y1)) = (x2 y0 (x3 x4 y2))).
Definition term60 (a0 : Type') (x0 : a0) (x1 : type1400 a0) (x2 : type1400 a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, forall y4 : a0, (~ (y0 = x0)) -> ((y1 = y2) /\ (~ (y3 = y4))) -> ~ ((x1 y1 (x2 y0 y3)) = (x1 y2 (x2 y0 y4))).
Definition term58 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((~ (y0 = y1)) /\ (~ (y2 = y3))) = (~ ((x0 (x1 y0 y2) (x1 y1 y3)) = (x0 (x1 y0 y3) (x1 y1 y2)))).
Definition term56 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : type1400 a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, ((~ (x1 = y0)) /\ (~ (y1 = y2))) = (~ ((x0 (x2 x1 y1) (x2 y0 y2)) = (x0 (x2 x1 y2) (x2 y0 y1)))).
Definition term35 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) (x2 : a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 (x1 x2 y1) (x1 y0 y2)) = (x0 (x1 x2 y2) (x1 y0 y1))) = ((x2 = y0) \/ (y1 = y2)).
Definition term31 (a0 : Type') (x0 : type1400 a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x0 y0 y1) = (x0 y0 y2)) = (y1 = y2).
Definition term30 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) := forall y0 : a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((x0 (x1 y0 y2) (x1 y1 y3)) = (x0 (x1 y0 y3) (x1 y1 y2))) = ((y0 = y1) \/ (y2 = y3)).
Definition term39 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) (x2 : a0) (x3 : a0) (x4 : a0) := forall y0 : a0, ((x0 (x1 x2 x4) (x1 x3 y0)) = (x0 (x1 x2 y0) (x1 x3 x4))) = ((x2 = x3) \/ (x4 = y0)).
Definition term62 (a0 : Type') (x0 : a0) (x1 : type1400 a0) (x2 : type1400 a0) := True /\ (forall y0 : a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, forall y4 : a0, (~ (y0 = x0)) -> ((y1 = y2) /\ (~ (y3 = y4))) -> ~ ((x1 y1 (x2 y0 y3)) = (x1 y2 (x2 y0 y4)))).
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) := @eq Prop (~ ((x0 = x1) \/ (x2 = x3))).
Definition term59 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) := and (forall y0 : a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((~ (y0 = y1)) /\ (~ (y2 = y3))) = (~ ((x0 (x1 y0 y2) (x1 y1 y3)) = (x0 (x1 y0 y3) (x1 y1 y2))))).
Definition term82 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1400 a0) (x3 : type1400 a0) (x4 : a0) (x5 : a0) (x6 : a0) (x7 : a0) (x8 : Prop) := forall y0 : Prop, ((~ (~ ((x2 x0 (x3 x5 x7)) = (x2 x1 (x3 x5 x6))))) = x8) -> (x8 -> (~ (((x2 (x3 x4 x6) (x3 x5 x7)) = (x2 (x3 x4 x7) (x3 x5 x6))) = ((x4 = x5) \/ (x6 = x7)))) = y0) -> ((~ (~ ((x2 x0 (x3 x5 x7)) = (x2 x1 (x3 x5 x6))))) -> ~ (((x2 (x3 x4 x6) (x3 x5 x7)) = (x2 (x3 x4 x7) (x3 x5 x6))) = ((x4 = x5) \/ (x6 = x7)))) = (x8 -> y0).
Definition term76 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term14 (x0 : Prop) (x1 : Prop) := and (((~ x0) \/ (~ x1)) = (~ (x0 /\ x1))).
Definition term78 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1400 a0) (x3 : type1400 a0) (x4 : a0) (x5 : a0) (x6 : a0) (x7 : a0) := forall y0 : Prop, forall y1 : Prop, ((~ (~ ((x2 x0 (x3 x5 x7)) = (x2 x1 (x3 x5 x6))))) = y0) -> (y0 -> (~ (((x2 (x3 x4 x6) (x3 x5 x7)) = (x2 (x3 x4 x7) (x3 x5 x6))) = ((x4 = x5) \/ (x6 = x7)))) = y1) -> ((~ (~ ((x2 x0 (x3 x5 x7)) = (x2 x1 (x3 x5 x6))))) -> ~ (((x2 (x3 x4 x6) (x3 x5 x7)) = (x2 (x3 x4 x7) (x3 x5 x6))) = ((x4 = x5) \/ (x6 = x7)))) = (y0 -> y1).
Definition term77 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term26 := forall y0 : Prop, forall y1 : Prop, (((~ y0) \/ (~ y1)) = (~ (y0 /\ y1))) /\ (((~ y0) /\ (~ y1)) = (~ (y0 \/ y1))).
Definition term25 := forall y0 : Prop, forall y1 : Prop, ((~ (y0 /\ y1)) = ((~ y0) \/ (~ y1))) /\ ((~ (y0 \/ y1)) = ((~ y0) /\ (~ y1))).
Definition term8 := forall y0 : Prop, forall y1 : Prop, (y1 -> y0) = ((~ y0) -> ~ y1).
Definition term7 := forall y0 : Prop, forall y1 : Prop, ((~ y0) -> ~ y1) = (y1 -> y0).
Definition term90 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) (x2 : a0) (x3 : a0) := x0 (x1 x2 x3).
Definition term63 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term93 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term95 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1400 a0) (x3 : a0) (x4 : a0) (x5 : type1400 a0) (x6 : a0) (x7 : a0) := (((x5 x6 x4) = (x5 x6 x7)) -> (~ (((x2 (x5 x3 x7) (x5 x6 x4)) = (x2 (x5 x3 x4) (x5 x6 x7))) = ((x3 = x6) \/ (x7 = x4)))) = True) -> ((~ (~ ((x2 x0 (x5 x6 x4)) = (x2 x1 (x5 x6 x7))))) -> ~ (((x2 (x5 x3 x7) (x5 x6 x4)) = (x2 (x5 x3 x4) (x5 x6 x7))) = ((x3 = x6) \/ (x7 = x4)))) = (((x5 x6 x4) = (x5 x6 x7)) -> True).
Definition term29 (a0 : Type') (x0 : type1400 a0) (x1 : a0) := forall y0 : a0, (x0 x1 y0) = x1.
Definition term79 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1400 a0) (x3 : a0) (x4 : type1400 a0) (x5 : a0) (x6 : a0) := ~ (~ ((x2 x0 (x4 x5 x1)) = (x2 x3 (x4 x5 x6)))).
Definition term88 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1400 a0) (x3 : a0) (x4 : a0) (x5 : type1400 a0) (x6 : a0) (x7 : a0) (x8 : Prop) := ((~ (~ ((x2 x0 (x5 x6 x4)) = (x2 x1 (x5 x6 x7))))) = ((x5 x6 x4) = (x5 x6 x7))) -> (((x5 x6 x4) = (x5 x6 x7)) -> (~ (((x2 (x5 x3 x7) (x5 x6 x4)) = (x2 (x5 x3 x4) (x5 x6 x7))) = ((x3 = x6) \/ (x7 = x4)))) = x8) -> ((~ (~ ((x2 x0 (x5 x6 x4)) = (x2 x1 (x5 x6 x7))))) -> ~ (((x2 (x5 x3 x7) (x5 x6 x4)) = (x2 (x5 x3 x4) (x5 x6 x7))) = ((x3 = x6) \/ (x7 = x4)))) = (((x5 x6 x4) = (x5 x6 x7)) -> x8).
Definition term44 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) (x3 : a0) := ~ ((x0 = x1) \/ (x2 = x3)).
Definition term47 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : a0) (x3 : type1400 a0) (x4 : a0) (x5 : a0) := ~ ((x0 (x3 x1 x5) (x3 x4 x2)) = (x0 (x3 x1 x2) (x3 x4 x5))).
Definition term81 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1400 a0) (x3 : type1400 a0) (x4 : a0) (x5 : a0) (x6 : a0) (x7 : a0) (x8 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (~ ((x2 x0 (x3 x5 x7)) = (x2 x1 (x3 x5 x6))))) = y0) -> (y0 -> (~ (((x2 (x3 x4 x6) (x3 x5 x7)) = (x2 (x3 x4 x7) (x3 x5 x6))) = ((x4 = x5) \/ (x6 = x7)))) = y1) -> ((~ (~ ((x2 x0 (x3 x5 x7)) = (x2 x1 (x3 x5 x6))))) -> ~ (((x2 (x3 x4 x6) (x3 x5 x7)) = (x2 (x3 x4 x7) (x3 x5 x6))) = ((x4 = x5) \/ (x6 = x7)))) = (y0 -> y1)) x8.
Definition term100 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : type1400 a0) (x3 : a0) (x4 : type1400 a0) (x5 : a0) := forall y0 : a0, forall y1 : a0, (~ (x5 = x0)) -> ((x1 = x3) /\ (~ (y0 = y1))) -> ~ ((x2 x1 (x4 x5 y0)) = (x2 x3 (x4 x5 y1))).
Definition term70 (a0 : Type') (x0 : type1400 a0) (x1 : a0) := forall y0 : a0, forall y1 : a0, ((x0 x1 y0) = (x0 x1 y1)) = (y0 = y1).
Definition term54 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : type1400 a0) (x3 : a0) := forall y0 : a0, forall y1 : a0, ((~ (x1 = x3)) /\ (~ (y0 = y1))) = (~ ((x0 (x2 x1 y0) (x2 x3 y1)) = (x0 (x2 x1 y1) (x2 x3 y0)))).
Definition term37 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) (x2 : a0) (x3 : a0) := forall y0 : a0, forall y1 : a0, ((x0 (x1 x2 y0) (x1 x3 y1)) = (x0 (x1 x2 y1) (x1 x3 y0))) = ((x2 = x3) \/ (y0 = y1)).
Definition term36 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) (x2 : a0) (x3 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0, ((x0 (x1 x2 y1) (x1 y0 y2)) = (x0 (x1 x2 y2) (x1 y0 y1))) = ((x2 = y0) \/ (y1 = y2))) x3.
Definition term1 (x0 : Prop) := fun y0 : Prop => ((~ x0) -> ~ y0) = (y0 -> x0).
Definition term72 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : a0) := forall y0 : a0, ((x0 x1 x2) = (x0 x1 y0)) = (x2 = y0).
Definition term103 (a0 : Type') (x0 : a0) (x1 : type1400 a0) (x2 : type1400 a0) := ((forall y0 : a0, (x2 x0 y0) = x0) /\ ((forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x1 y0 y1) = (x1 y0 y2)) = (y1 = y2)) /\ (forall y0 : a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((x1 (x2 y0 y2) (x2 y1 y3)) = (x1 (x2 y0 y3) (x2 y1 y2))) = ((y0 = y1) \/ (y2 = y3))))) -> (forall y0 : a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((~ (y0 = y1)) /\ (~ (y2 = y3))) = (~ ((x1 (x2 y0 y2) (x2 y1 y3)) = (x1 (x2 y0 y3) (x2 y1 y2))))) /\ (forall y0 : a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, forall y4 : a0, (~ (y0 = x0)) -> ((y1 = y2) /\ (~ (y3 = y4))) -> ~ ((x1 y1 (x2 y0 y3)) = (x1 y2 (x2 y0 y4)))).
Definition term96 (a0 : Type') (x0 : a0) (x1 : type1400 a0) (x2 : a0) (x3 : a0) := ((x1 x2 x0) = (x1 x2 x3)) -> True.
Definition term18 (x0 : Prop) (x1 : Prop) := (((~ x0) \/ (~ x1)) = (~ (x0 /\ x1))) /\ (((~ x0) /\ (~ x1)) = (~ (x0 \/ x1))).
Definition term104 (a0 : Type') (x0 : type1400 a0) (x1 : type1400 a0) := forall y0 : a0, ((forall y1 : a0, (x1 y0 y1) = y0) /\ ((forall y1 : a0, forall y2 : a0, forall y3 : a0, ((x0 y1 y2) = (x0 y1 y3)) = (y2 = y3)) /\ (forall y1 : a0, forall y2 : a0, forall y3 : a0, forall y4 : a0, ((x0 (x1 y1 y3) (x1 y2 y4)) = (x0 (x1 y1 y4) (x1 y2 y3))) = ((y1 = y2) \/ (y3 = y4))))) -> (forall y1 : a0, forall y2 : a0, forall y3 : a0, forall y4 : a0, ((~ (y1 = y2)) /\ (~ (y3 = y4))) = (~ ((x0 (x1 y1 y3) (x1 y2 y4)) = (x0 (x1 y1 y4) (x1 y2 y3))))) /\ (forall y1 : a0, forall y2 : a0, forall y3 : a0, forall y4 : a0, forall y5 : a0, (~ (y1 = y0)) -> ((y2 = y3) /\ (~ (y4 = y5))) -> ~ ((x0 y2 (x1 y1 y4)) = (x0 y3 (x1 y1 y5)))).
Definition term69 (a0 : Type') (x0 : type1400 a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0, ((x0 y0 y1) = (x0 y0 y2)) = (y1 = y2)) x1.
Definition term33 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (((~ x0) \/ (~ y0)) = (~ (x0 /\ y0))) /\ (((~ x0) /\ (~ y0)) = (~ (x0 \/ y0)))) x1.
Definition term50 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : type1400 a0) (x3 : a0) (x4 : a0) := forall y0 : a0, ((~ (x1 = x3)) /\ (~ (x4 = y0))) = (~ ((x0 (x2 x1 x4) (x2 x3 y0)) = (x0 (x2 x1 y0) (x2 x3 x4)))).
Definition term27 (a0 : Type') (x0 : a0) (x1 : type1400 a0) (x2 : type1400 a0) := (forall y0 : a0, (x2 x0 y0) = x0) /\ ((forall y0 : a0, forall y1 : a0, forall y2 : a0, ((x1 y0 y1) = (x1 y0 y2)) = (y1 = y2)) /\ (forall y0 : a0, forall y1 : a0, forall y2 : a0, forall y3 : a0, ((x1 (x2 y0 y2) (x2 y1 y3)) = (x1 (x2 y0 y3) (x2 y1 y2))) = ((y0 = y1) \/ (y2 = y3)))).
Definition term105 (a0 : Type') (x0 : type1400 a0) := forall y0 : type1400 a0, forall y1 : a0, ((forall y2 : a0, (y0 y1 y2) = y1) /\ ((forall y2 : a0, forall y3 : a0, forall y4 : a0, ((x0 y2 y3) = (x0 y2 y4)) = (y3 = y4)) /\ (forall y2 : a0, forall y3 : a0, forall y4 : a0, forall y5 : a0, ((x0 (y0 y2 y4) (y0 y3 y5)) = (x0 (y0 y2 y5) (y0 y3 y4))) = ((y2 = y3) \/ (y4 = y5))))) -> (forall y2 : a0, forall y3 : a0, forall y4 : a0, forall y5 : a0, ((~ (y2 = y3)) /\ (~ (y4 = y5))) = (~ ((x0 (y0 y2 y4) (y0 y3 y5)) = (x0 (y0 y2 y5) (y0 y3 y4))))) /\ (forall y2 : a0, forall y3 : a0, forall y4 : a0, forall y5 : a0, forall y6 : a0, (~ (y2 = y1)) -> ((y3 = y4) /\ (~ (y5 = y6))) -> ~ ((x0 y3 (y0 y2 y5)) = (x0 y4 (y0 y2 y6)))).
Definition term20 (x0 : Prop) := fun y0 : Prop => (((~ x0) \/ (~ y0)) = (~ (x0 /\ y0))) /\ (((~ x0) /\ (~ y0)) = (~ (x0 \/ y0))).
Definition term92 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : a0) (x3 : type1400 a0) (x4 : a0) (x5 : a0) := @eq Prop ((x0 (x3 x1 x5) (x3 x4 x2)) = (x0 (x3 x1 x2) (x3 x4 x5))).
Definition term2 (x0 : Prop) := fun y0 : Prop => (y0 -> x0) = ((~ x0) -> ~ y0).
Definition term87 (a0 : Type') (x0 : type1400 a0) (x1 : a0) (x2 : type1400 a0) (x3 : a0) (x4 : a0) := @eq a0 (x0 x1 (x2 x3 x4)).
