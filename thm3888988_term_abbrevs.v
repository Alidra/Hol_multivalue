Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := (~ (x2 = x0)) /\ ((~ (x1 x2)) /\ x3).
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := (~ (x1 = x0)) /\ ((~ (@IN a0 x1 x2)) /\ x3).
Definition term0 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term61 (a0 : Type') := fun y0 : Prop => forall y1 : a0, forall y2 : a0 -> Prop, forall y3 : a0, ((~ ((y1 = y3) \/ (y2 y1))) /\ y0) = ((~ (y1 = y3)) /\ ((~ (y2 y1)) /\ y0)).
Definition term60 (a0 : Type') := fun y0 : Prop => forall y1 : a0, forall y2 : a0 -> Prop, forall y3 : a0, (~ (((~ ((y1 = y3) \/ (y2 y1))) /\ y0) = ((~ (y1 = y3)) /\ ((~ (y2 y1)) /\ y0)))) -> False.
Definition term95 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0, (~ ((y0 = y2) \/ (y1 y0))) = ((~ (y0 = y2)) /\ (~ (y1 y0))).
Definition term77 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0, ((~ ((y0 = y2) \/ (y1 y0))) /\ False) = ((~ (y0 = y2)) /\ ((~ (y1 y0)) /\ False)).
Definition term73 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0, ((~ ((y0 = y2) \/ (y1 y0))) /\ True) = ((~ (y0 = y2)) /\ ((~ (y1 y0)) /\ True)).
Definition term59 (a0 : Type') (x0 : Prop) := forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0, ((~ ((y0 = y2) \/ (y1 y0))) /\ x0) = ((~ (y0 = y2)) /\ ((~ (y1 y0)) /\ x0)).
Definition term58 (a0 : Type') (x0 : Prop) := forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0, (~ (((~ ((y0 = y2) \/ (y1 y0))) /\ x0) = ((~ (y0 = y2)) /\ ((~ (y1 y0)) /\ x0)))) -> False.
Definition term147 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (~ (((~ ((x0 = y1) \/ (y0 x0))) /\ x1) = ((~ (x0 = y1)) /\ ((~ (y0 x0)) /\ x1)))) -> False) x2.
Definition term142 := (~ False) -> False.
Definition term66 (a0 : Type') := forall y0 : Prop, (fun y1 : Prop => forall y2 : a0, forall y3 : a0 -> Prop, forall y4 : a0, ((~ ((y2 = y4) \/ (y3 y2))) /\ y1) = ((~ (y2 = y4)) /\ ((~ (y3 y2)) /\ y1))) y0.
Definition term125 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((x2 = x0) \/ (x1 x2)) /\ ((~ (x2 = x0)) /\ (~ (x1 x2))).
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (@IN a0 x0 (@INSERT a0 x1 (@EMPTY a0))).
Definition term1 (a0 : Type') (x0 : a0) := and (~ (@IN a0 x0 (@EMPTY a0))).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) := (~ (x0 x1)) /\ x2.
Definition term127 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x2 = x0) \/ (x1 x2))) /\ (~ ((~ (x2 = x0)) /\ (~ (x1 x2)))).
Definition term71 (a0 : Type') := @eq Prop (forall y0 : Prop, forall y1 : a0, forall y2 : a0 -> Prop, forall y3 : a0, ((~ ((y1 = y3) \/ (y2 y1))) /\ y0) = ((~ (y1 = y3)) /\ ((~ (y2 y1)) /\ y0))).
Definition term47 (x0 : Prop) := ~ (~ x0).
Definition term134 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x1.
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x2 = x0) \/ (x1 x2).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, ((~ ((x1 = y0) \/ (x0 x1))) /\ False) = ((~ (x1 = y0)) /\ ((~ (x0 x1)) /\ False)).
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, ((~ ((x1 = y0) \/ (x0 x1))) /\ True) = ((~ (x1 = y0)) /\ ((~ (x0 x1)) /\ True)).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term106 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := (~ (@IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) /\ x2.
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term146 (a0 : Type') (x0 : Prop) (x1 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, forall y2 : a0, (~ (((~ ((y0 = y2) \/ (y1 y0))) /\ x0) = ((~ (y0 = y2)) /\ ((~ (y1 y0)) /\ x0)))) -> False) x1.
Definition term128 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((~ (x2 = x0)) /\ (~ (x1 x2))) /\ ((x2 = x0) \/ (x1 x2)).
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term69 (a0 : Type') := fun y0 : Prop => (fun y1 : Prop => forall y2 : a0, forall y3 : a0 -> Prop, forall y4 : a0, ((~ ((y2 = y4) \/ (y3 y2))) /\ y1) = ((~ (y2 = y4)) /\ ((~ (y3 y2)) /\ y1))) y0.
Definition term40 (x0 : Prop) := (~ x0) -> False.
Definition term114 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ ((~ ((x2 = x0) \/ (x1 x2))) = ((~ (x2 = x0)) /\ (~ (x1 x2))))) -> False.
Definition term41 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := (~ (((~ ((x2 = x0) \/ (x1 x2))) /\ x3) = ((~ (x2 = x0)) /\ ((~ (x1 x2)) /\ x3)))) -> False.
Definition term148 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) (x3 : a0) := (fun y0 : a0 => (~ (((~ ((x1 = y0) \/ (x0 x1))) /\ x2) = ((~ (x1 = y0)) /\ ((~ (x0 x1)) /\ x2)))) -> False) x3.
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) /\ False.
Definition term2 (a0 : Type') (x0 : a0) (x1 : Prop) := (~ (@IN a0 x0 (@EMPTY a0))) /\ x1.
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) \/ False.
Definition term105 (a0 : Type') := forall y0 : a0, True.
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) := forall y0 : a0, ((~ ((x1 = y0) \/ (x0 x1))) /\ x2) = ((~ (x1 = y0)) /\ ((~ (x0 x1)) /\ x2)).
Definition term130 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := or (((~ (x2 = x0)) /\ (~ (x1 x2))) /\ ((x2 = x0) \/ (x1 x2))).
Definition term111 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term112 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, forall y2 : a0, ((~ ((y0 = y2) \/ (y1 y0))) /\ False) = ((~ (y0 = y2)) /\ ((~ (y1 y0)) /\ False)).
Definition term94 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, forall y2 : a0, (~ ((y0 = y2) \/ (y1 y0))) = ((~ (y0 = y2)) /\ (~ (y1 y0))).
Definition term93 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, forall y2 : a0, ((~ ((y0 = y2) \/ (y1 y0))) /\ True) = ((~ (y0 = y2)) /\ ((~ (y1 y0)) /\ True)).
Definition term57 (a0 : Type') (x0 : Prop) := fun y0 : a0 => forall y1 : a0 -> Prop, forall y2 : a0, ((~ ((y0 = y2) \/ (y1 y0))) /\ x0) = ((~ (y0 = y2)) /\ ((~ (y1 y0)) /\ x0)).
Definition term56 (a0 : Type') (x0 : Prop) := fun y0 : a0 => forall y1 : a0 -> Prop, forall y2 : a0, (~ (((~ ((y0 = y2) \/ (y1 y0))) /\ x0) = ((~ (y0 = y2)) /\ ((~ (y1 y0)) /\ x0)))) -> False.
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (x0 x1)).
Definition term129 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := or ((~ ((x2 = x0) \/ (x1 x2))) /\ (~ ((~ (x2 = x0)) /\ (~ (x1 x2))))).
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term140 (x0 : Prop) := (~ x0) -> x0.
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := @eq Prop ((~ (x0 = x1)) /\ x2).
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := @eq Prop ((~ (@IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) /\ x2).
Definition term122 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := and (~ (~ ((x2 = x0) \/ (x1 x2)))).
Definition term102 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => ((~ ((x1 = y0) \/ (x0 x1))) /\ False) = ((~ (x1 = y0)) /\ ((~ (x0 x1)) /\ False)).
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := and (((~ (@IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)))) /\ x2) = ((~ (x0 = x1)) /\ x2)).
Definition term100 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x2 = x0)) /\ ((~ (x1 x2)) /\ False).
Definition term78 (a0 : Type') := (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0, ((~ ((y0 = y2) \/ (y1 y0))) /\ True) = ((~ (y0 = y2)) /\ ((~ (y1 y0)) /\ True))) /\ (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0, ((~ ((y0 = y2) \/ (y1 y0))) /\ False) = ((~ (y0 = y2)) /\ ((~ (y1 y0)) /\ False))).
Definition term115 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((~ ((x2 = x0) \/ (x1 x2))) = ((~ (x2 = x0)) /\ (~ (x1 x2)))).
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := ~ (~ (((~ ((x2 = x0) \/ (x1 x2))) /\ x3) = ((~ (x2 = x0)) /\ ((~ (x1 x2)) /\ x3)))).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) := forall y0 : a0, (~ (((~ ((x1 = y0) \/ (x0 x1))) /\ x2) = ((~ (x1 = y0)) /\ ((~ (x0 x1)) /\ x2)))) -> False.
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x2 = x0) \/ (x1 x2)).
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : Prop) := (~ (x0 = x1)) /\ x2.
Definition term65 (x0 : Prop -> Prop) := (x0 True) /\ (x0 False).
Definition term54 (a0 : Type') (x0 : a0) (x1 : Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (~ (((~ ((x0 = y1) \/ (y0 x0))) /\ x1) = ((~ (x0 = y1)) /\ ((~ (y0 x0)) /\ x1)))) -> False.
Definition term136 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term113 (a0 : Type') := (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0, (~ ((y0 = y2) \/ (y1 y0))) = ((~ (y0 = y2)) /\ (~ (y1 y0)))) /\ True.
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) /\ True.
Definition term120 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (~ (x2 = x0))) \/ (~ (~ (x1 x2))).
Definition term84 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x2 = x0)) /\ (~ (x1 x2)).
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := (((~ (@IN a0 x1 (@INSERT a0 x0 (@EMPTY a0)))) /\ x3) = ((~ (x1 = x0)) /\ x3)) /\ (((~ (@IN a0 x1 (@INSERT a0 x0 x2))) /\ x3) = ((~ (x1 = x0)) /\ ((~ (@IN a0 x1 x2)) /\ x3))).
Definition term42 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := ~ (((~ ((x2 = x0) \/ (x1 x2))) /\ x3) = ((~ (x2 = x0)) /\ ((~ (x1 x2)) /\ x3))).
Definition term43 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := ((~ (((~ ((x2 = x0) \/ (x1 x2))) /\ x3) = ((~ (x2 = x0)) /\ ((~ (x1 x2)) /\ x3)))) -> False) -> (~ (((~ ((x2 = x0) \/ (x1 x2))) /\ x3) = ((~ (x2 = x0)) /\ ((~ (x1 x2)) /\ x3)))) -> False.
Definition term25 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := (~ (@IN a0 x0 (@INSERT a0 x1 x2))) /\ x3.
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (~ ((x1 = y0) \/ (x0 x1))) = ((~ (x1 = y0)) /\ (~ (x0 x1))).
Definition term107 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => forall y1 : a0, ((~ ((x0 = y1) \/ (y0 x0))) /\ False) = ((~ (x0 = y1)) /\ ((~ (y0 x0)) /\ False)).
Definition term90 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => forall y1 : a0, (~ ((x0 = y1) \/ (y0 x0))) = ((~ (x0 = y1)) /\ (~ (y0 x0))).
Definition term89 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => forall y1 : a0, ((~ ((x0 = y1) \/ (y0 x0))) /\ True) = ((~ (x0 = y1)) /\ ((~ (y0 x0)) /\ True)).
Definition term53 (a0 : Type') (x0 : a0) (x1 : Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ((~ ((x0 = y1) \/ (y0 x0))) /\ x1) = ((~ (x0 = y1)) /\ ((~ (y0 x0)) /\ x1)).
Definition term103 (a0 : Type') := fun y0 : a0 => True.
Definition term97 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x2 = x0) \/ (x1 x2))) /\ False.
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0) := and (~ (x0 = x1)).
Definition term137 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (y0 = x0)) x1).
Definition term23 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := and (~ (@IN a0 x0 (@INSERT a0 x1 x2))).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) := fun y0 : a0 => ((~ ((x1 = y0) \/ (x0 x1))) /\ x2) = ((~ (x1 = y0)) /\ ((~ (x0 x1)) /\ x2)).
Definition term72 (a0 : Type') := (fun y0 : Prop => forall y1 : a0, forall y2 : a0 -> Prop, forall y3 : a0, ((~ ((y1 = y3) \/ (y2 y1))) /\ y0) = ((~ (y1 = y3)) /\ ((~ (y2 y1)) /\ y0))) True.
Definition term80 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((~ ((x2 = x0) \/ (x1 x2))) /\ True).
Definition term70 (a0 : Type') := @eq Prop (forall y0 : Prop, (fun y1 : Prop => forall y2 : a0, forall y3 : a0 -> Prop, forall y4 : a0, ((~ ((y2 = y4) \/ (y3 y2))) /\ y1) = ((~ (y2 = y4)) /\ ((~ (y3 y2)) /\ y1))) y0).
Definition term24 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := and (~ ((x2 = x0) \/ (x1 x2))).
Definition term96 (a0 : Type') := and (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0, (~ ((y0 = y2) \/ (y1 y0))) = ((~ (y0 = y2)) /\ (~ (y1 y0)))).
Definition term75 (a0 : Type') := and (forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0, ((~ ((y0 = y2) \/ (y1 y0))) /\ True) = ((~ (y0 = y2)) /\ ((~ (y1 y0)) /\ True))).
Definition term108 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term83 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x2 = x0)) /\ ((~ (x1 x2)) /\ True).
Definition term44 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := (((~ (((~ ((x2 = x0) \/ (x1 x2))) /\ x3) = ((~ (x2 = x0)) /\ ((~ (x1 x2)) /\ x3)))) -> False) -> (~ (((~ ((x2 = x0) \/ (x1 x2))) /\ x3) = ((~ (x2 = x0)) /\ ((~ (x1 x2)) /\ x3)))) -> False) -> (~ (((~ ((x2 = x0) \/ (x1 x2))) /\ x3) = ((~ (x2 = x0)) /\ ((~ (x1 x2)) /\ x3)))) -> False.
Definition term126 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := and ((~ (x2 = x0)) /\ (~ (x1 x2))).
Definition term63 (a0 : Type') := forall y0 : Prop, forall y1 : a0, forall y2 : a0 -> Prop, forall y3 : a0, ((~ ((y1 = y3) \/ (y2 y1))) /\ y0) = ((~ (y1 = y3)) /\ ((~ (y2 y1)) /\ y0)).
Definition term62 (a0 : Type') := forall y0 : Prop, forall y1 : a0, forall y2 : a0 -> Prop, forall y3 : a0, (~ (((~ ((y1 = y3) \/ (y2 y1))) /\ y0) = ((~ (y1 = y3)) /\ ((~ (y2 y1)) /\ y0)))) -> False.
Definition term101 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x0 = x1)) /\ False.
Definition term138 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (~ (x0 = x1)).
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term67 (a0 : Type') := ((fun y0 : Prop => forall y1 : a0, forall y2 : a0 -> Prop, forall y3 : a0, ((~ ((y1 = y3) \/ (y2 y1))) /\ y0) = ((~ (y1 = y3)) /\ ((~ (y2 y1)) /\ y0))) True) /\ ((fun y0 : Prop => forall y1 : a0, forall y2 : a0 -> Prop, forall y3 : a0, ((~ ((y1 = y3) \/ (y2 y1))) /\ y0) = ((~ (y1 = y3)) /\ ((~ (y2 y1)) /\ y0))) False).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => ((~ ((x1 = y0) \/ (x0 x1))) /\ True) = ((~ (x1 = y0)) /\ ((~ (x0 x1)) /\ True)).
Definition term38 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := True /\ (((~ ((x2 = x0) \/ (x1 x2))) /\ x3) = ((~ (x2 = x0)) /\ ((~ (x1 x2)) /\ x3))).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : Prop) := fun y0 : a0 => (~ (((~ ((x1 = y0) \/ (x0 x1))) /\ x2) = ((~ (x1 = y0)) /\ ((~ (x0 x1)) /\ x2)))) -> False.
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (~ ((x1 = y0) \/ (x0 x1))) = ((~ (x1 = y0)) /\ (~ (x0 x1))).
Definition term76 (a0 : Type') := (fun y0 : Prop => forall y1 : a0, forall y2 : a0 -> Prop, forall y3 : a0, ((~ ((y1 = y3) \/ (y2 y1))) /\ y0) = ((~ (y1 = y3)) /\ ((~ (y2 y1)) /\ y0))) False.
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := @eq Prop ((~ ((x2 = x0) \/ (x1 x2))) /\ x3).
Definition term27 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := @eq Prop ((~ (@IN a0 x0 (@INSERT a0 x1 x2))) /\ x3).
Definition term132 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (((~ (x2 = x0)) /\ (~ (x1 x2))) /\ ((x2 = x0) \/ (x1 x2))) \/ (((x2 = x0) \/ (x1 x2)) /\ ((~ (x2 = x0)) /\ (~ (x1 x2)))).
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := ~ (@IN a0 x0 (@INSERT a0 x1 x2)).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0) := and (~ (@IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)))).
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0) := (x1 = x0) \/ (@IN a0 x1 (@EMPTY a0)).
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)).
Definition term64 (x0 : Prop -> Prop) := forall y0 : Prop, x0 y0.
Definition term139 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term116 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ (~ ((x2 = x0) \/ (x1 x2))).
Definition term133 (a0 : Type') (x0 : a0) := fun y0 : a0 => ~ (y0 = x0).
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term79 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x2 = x0) \/ (x1 x2))) /\ True.
Definition term52 (a0 : Type') (x0 : a0) (x1 : Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (~ (((~ ((x0 = y1) \/ (y0 x0))) /\ x1) = ((~ (x0 = y1)) /\ ((~ (y0 x0)) /\ x1)))) -> False.
Definition term119 (a0 : Type') (x0 : a0) (x1 : a0) := or (~ (~ (x0 = x1))).
Definition term124 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (~ ((x2 = x0) \/ (x1 x2)))) /\ ((~ (x2 = x0)) /\ (~ (x1 x2))).
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := (~ ((x2 = x0) \/ (x1 x2))) /\ x3.
Definition term145 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0, forall y2 : a0 -> Prop, forall y3 : a0, (~ (((~ ((y1 = y3) \/ (y2 y1))) /\ y0) = ((~ (y1 = y3)) /\ ((~ (y2 y1)) /\ y0)))) -> False) x0.
Definition term68 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0, forall y2 : a0 -> Prop, forall y3 : a0, ((~ ((y1 = y3) \/ (y2 y1))) /\ y0) = ((~ (y1 = y3)) /\ ((~ (y2 y1)) /\ y0))) x0.
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (~ (@IN a0 x0 x1)).
Definition term81 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop (~ ((x2 = x0) \/ (x1 x2))).
Definition term45 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : Prop) := (((~ (((~ ((x2 = x0) \/ (x1 x2))) /\ x3) = ((~ (x2 = x0)) /\ ((~ (x1 x2)) /\ x3)))) -> False) -> (~ (((~ ((x2 = x0) \/ (x1 x2))) /\ x3) = ((~ (x2 = x0)) /\ ((~ (x1 x2)) /\ x3)))) -> False) -> ((~ (((~ ((x2 = x0) \/ (x1 x2))) /\ x3) = ((~ (x2 = x0)) /\ ((~ (x1 x2)) /\ x3)))) -> False) -> (~ (((~ ((x2 = x0) \/ (x1 x2))) /\ x3) = ((~ (x2 = x0)) /\ ((~ (x1 x2)) /\ x3)))) -> False.
Definition term39 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := (((~ (@IN a0 x1 (@EMPTY a0))) /\ x3) = x3) /\ ((((~ (@IN a0 x1 (@INSERT a0 x0 (@EMPTY a0)))) /\ x3) = ((~ (x1 = x0)) /\ x3)) /\ (((~ (@IN a0 x1 (@INSERT a0 x0 x2))) /\ x3) = ((~ (x1 = x0)) /\ ((~ (@IN a0 x1 x2)) /\ x3)))).
Definition term121 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((~ (x2 = x0)) /\ (~ (x1 x2))).
Definition term3 (a0 : Type') (x0 : a0) (x1 : Prop) := @eq Prop ((~ (@IN a0 x0 (@EMPTY a0))) /\ x1).
Definition term4 (a0 : Type') (x0 : a0) (x1 : Prop) := and (((~ (@IN a0 x0 (@EMPTY a0))) /\ x1) = x1).
Definition term123 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := and ((x2 = x0) \/ (x1 x2)).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (~ (x0 x1)).
Definition term143 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term141 (a0 : Type') (x0 : a0) := (x0 = x0) -> False.
Definition term109 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, forall y1 : a0, ((~ ((x0 = y1) \/ (y0 x0))) /\ False) = ((~ (x0 = y1)) /\ ((~ (y0 x0)) /\ False)).
Definition term92 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, forall y1 : a0, (~ ((x0 = y1) \/ (y0 x0))) = ((~ (x0 = y1)) /\ (~ (y0 x0))).
Definition term91 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, forall y1 : a0, ((~ ((x0 = y1) \/ (y0 x0))) /\ True) = ((~ (x0 = y1)) /\ ((~ (y0 x0)) /\ True)).
Definition term55 (a0 : Type') (x0 : a0) (x1 : Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ((~ ((x0 = y1) \/ (y0 x0))) /\ x1) = ((~ (x0 = y1)) /\ ((~ (y0 x0)) /\ x1)).
Definition term131 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ((~ ((x2 = x0) \/ (x1 x2))) /\ (~ ((~ (x2 = x0)) /\ (~ (x1 x2))))) \/ ((~ (~ ((x2 = x0) \/ (x1 x2)))) /\ ((~ (x2 = x0)) /\ (~ (x1 x2)))).
Definition term33 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := (~ (@IN a0 x0 x1)) /\ x2.
Definition term74 (a0 : Type') := and ((fun y0 : Prop => forall y1 : a0, forall y2 : a0 -> Prop, forall y3 : a0, ((~ ((y1 = y3) \/ (y2 y1))) /\ y0) = ((~ (y1 = y3)) /\ ((~ (y2 y1)) /\ y0))) True).
Definition term117 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (~ (x0 = x1)).
Definition term98 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((~ ((x2 = x0) \/ (x1 x2))) /\ False).
Definition term135 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x0.
Definition term110 (a0 : Type') := forall y0 : a0 -> Prop, True.
