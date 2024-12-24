Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term158 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (@UNION a0 (@INSERT a0 y0 y1) y2) = (@COND (a0 -> Prop) (@IN a0 y0 y2) (@UNION a0 y1 y2) (@INSERT a0 y0 (@UNION a0 y1 y2))).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term87 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ (~ ((x1 x3) \/ (x2 x3)))).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : a0) (x3 : a0 -> Prop) (x4 : a0 -> Prop) (x5 : a0 -> Prop) := (x1 -> (fun y0 : a0 -> Prop => (@UNION a0 (@INSERT a0 x2 x3) x4) = y0) x0) /\ ((~ x1) -> (fun y0 : a0 -> Prop => (@UNION a0 (@INSERT a0 x2 x3) x4) = y0) x5).
Definition term98 := (~ False) -> False.
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) \/ (@IN a0 x1 x2).
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 x2) -> forall y0 : a0, (@IN a0 y0 (@UNION a0 (@INSERT a0 x0 x1) x2)) = (@IN a0 y0 (@UNION a0 x1 x2)).
Definition term105 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 (@UNION a0 x2 x3)).
Definition term38 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((x3 = x0) \/ (x1 x3)) \/ (x2 x3).
Definition term55 (x0 : Prop) := ~ (~ x0).
Definition term89 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ (~ ((x1 x3) \/ (x2 x3)))) \/ ((~ (((x3 = x0) \/ (x1 x3)) \/ (x2 x3))) /\ ((x1 x3) \/ (x2 x3))).
Definition term143 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ ((~ (x3 = x0)) /\ ((~ (x1 x3)) /\ (~ (x2 x3))))) \/ ((((~ (x3 = x0)) /\ (~ (x1 x3))) /\ (~ (x2 x3))) /\ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3)))).
Definition term146 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x1.
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) \/ (x1 x2)).
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x2 = x0) \/ (x1 x2).
Definition term33 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (x2 x0) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((x1 y0) \/ (x2 y0)).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (~ (@IN a0 x0 x1)).
Definition term129 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (~ (y0 y2)) -> forall y3 : a0, (((y3 = y2) \/ (y1 y3)) \/ (y0 y3)) = ((y3 = y2) \/ ((y1 y3) \/ (y0 y3))).
Definition term128 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (~ ((~ (y0 y2)) -> forall y3 : a0, (((y3 = y2) \/ (y1 y3)) \/ (y0 y3)) = ((y3 = y2) \/ ((y1 y3) \/ (y0 y3))))) -> False.
Definition term67 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (y0 y2) -> forall y3 : a0, (((y3 = y2) \/ (y1 y3)) \/ (y0 y3)) = ((y1 y3) \/ (y0 y3)).
Definition term66 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (~ ((y0 y2) -> forall y3 : a0, (((y3 = y2) \/ (y1 y3)) \/ (y0 y3)) = ((y1 y3) \/ (y0 y3)))) -> False.
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term48 (x0 : Prop) := (~ x0) -> False.
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (~ (x0 x1)).
Definition term130 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) = ((x3 = x0) \/ ((x1 x3) \/ (x2 x3))))) -> False.
Definition term68 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) = ((x1 x3) \/ (x2 x3)))) -> False.
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ((@IN a0 x0 x2) -> (fun y0 : a0 -> Prop => (@UNION a0 (@INSERT a0 x0 x1) x2) = y0) (@UNION a0 x1 x2)) /\ ((~ (@IN a0 x0 x2)) -> (fun y0 : a0 -> Prop => (@UNION a0 (@INSERT a0 x0 x1) x2) = y0) (@INSERT a0 x0 (@UNION a0 x1 x2))).
Definition term119 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (~ (x1 y0)) -> forall y1 : a0, (((y1 = y0) \/ (x0 y1)) \/ (x1 y1)) = ((y1 = y0) \/ ((x0 y1) \/ (x1 y1))).
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (~ ((~ (x1 y0)) -> forall y1 : a0, (((y1 = y0) \/ (x0 y1)) \/ (x1 y1)) = ((y1 = y0) \/ ((x0 y1) \/ (x1 y1))))) -> False.
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (~ ((x1 y0) -> forall y1 : a0, (((y1 = y0) \/ (x0 y1)) \/ (x1 y1)) = ((x0 y1) \/ (x1 y1)))) -> False.
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x1 y0) -> forall y1 : a0, (((y1 = y0) \/ (x0 y1)) \/ (x1 y1)) = ((x0 y1) \/ (x1 y1)).
Definition term153 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (~ ((~ (y0 y2)) -> forall y3 : a0, (((y3 = y2) \/ (y1 y3)) \/ (y0 y3)) = ((y3 = y2) \/ ((y1 y3) \/ (y0 y3))))) -> False) x0.
Definition term99 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (~ ((y0 y2) -> forall y3 : a0, (((y3 = y2) \/ (y1 y3)) \/ (y0 y3)) = ((y1 y3) \/ (y0 y3)))) -> False) x0.
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 x2) -> (fun y0 : a0 -> Prop => (@UNION a0 (@INSERT a0 x0 x1) x2) = y0) (@UNION a0 x1 x2).
Definition term117 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ~ (~ ((~ (x2 x0)) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))))).
Definition term45 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((x1 y0) \/ (x2 y0)).
Definition term23 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := @IN a0 x0 (@UNION a0 (@INSERT a0 x1 x2) x3).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term96 (x0 : Prop) := (~ x0) -> x0.
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := and ((@IN a0 x0 x2) -> (@UNION a0 (@INSERT a0 x0 x1) x2) = (@UNION a0 x1 x2)).
Definition term76 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((~ (x3 = x0)) /\ (~ (x1 x3))) /\ (~ (x2 x3)).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term54 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ~ (~ ((x2 x0) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((x1 y0) \/ (x2 y0)))).
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 -> Prop => (@UNION a0 (@INSERT a0 x0 x1) x2) = y0.
Definition term135 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3))).
Definition term120 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (~ ((~ (x1 y0)) -> forall y1 : a0, (((y1 = y0) \/ (x0 y1)) \/ (x1 y1)) = ((y1 = y0) \/ ((x0 y1) \/ (x1 y1))))) -> False.
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (~ ((x1 y0) -> forall y1 : a0, (((y1 = y0) \/ (x0 y1)) \/ (x1 y1)) = ((x0 y1) \/ (x1 y1)))) -> False.
Definition term44 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@UNION a0 (@INSERT a0 x0 x1) x2)) = (@IN a0 y0 (@UNION a0 x1 x2)).
Definition term106 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 (@UNION a0 x2 x3)).
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 x1 x2).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@UNION a0 (@INSERT a0 x0 x1) x2) = y0) (@UNION a0 x1 x2).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : type686 a0) (x3 : a0 -> Prop) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term70 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x2 = x0) \/ (x1 x2)).
Definition term124 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (~ ((~ (x0 y1)) -> forall y2 : a0, (((y2 = y1) \/ (y0 y2)) \/ (x0 y2)) = ((y2 = y1) \/ ((y0 y2) \/ (x0 y2))))) -> False.
Definition term62 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (~ ((x0 y1) -> forall y2 : a0, (((y2 = y1) \/ (y0 y2)) \/ (x0 y2)) = ((y0 y2) \/ (x0 y2)))) -> False.
Definition term148 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ (@IN a0 x0 x2)) -> (@UNION a0 (@INSERT a0 x0 x1) x2) = (@INSERT a0 x0 (@UNION a0 x1 x2)).
Definition term139 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ ((~ (x3 = x0)) /\ ((~ (x1 x3)) /\ (~ (x2 x3)))).
Definition term71 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x2 = x0)) /\ (~ (x1 x2)).
Definition term69 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) = ((x1 x3) \/ (x2 x3))).
Definition term88 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ ((~ (x1 x3)) /\ (~ (x2 x3)))).
Definition term114 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ((~ ((~ (x2 x0)) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))))) -> False) -> (~ ((~ (x2 x0)) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))))) -> False.
Definition term51 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ((~ ((x2 x0) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((x1 y0) \/ (x2 y0)))) -> False) -> (~ ((x2 x0) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((x1 y0) \/ (x2 y0)))) -> False.
Definition term50 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ~ ((x2 x0) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((x1 y0) \/ (x2 y0))).
Definition term110 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))).
Definition term83 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (((~ (x3 = x0)) /\ (~ (x1 x3))) /\ (~ (x2 x3))) /\ ((x1 x3) \/ (x2 x3)).
Definition term86 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ ((~ (x1 x3)) /\ (~ (x2 x3))).
Definition term132 (a0 : Type') (x0 : a0) (x1 : a0) := and (~ (x0 = x1)).
Definition term39 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@UNION a0 (@INSERT a0 x1 x2) x3)).
Definition term149 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (y0 = x0)) x1).
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term84 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := and (((x3 = x0) \/ (x1 x3)) \/ (x2 x3)).
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 x2) -> (@UNION a0 (@INSERT a0 x0 x1) x2) = (@UNION a0 x1 x2).
Definition term137 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (((~ (x3 = x0)) /\ (~ (x1 x3))) /\ (~ (x2 x3))) /\ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3))).
Definition term82 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (((x3 = x0) \/ (x1 x3)) \/ (x2 x3))) /\ ((x1 x3) \/ (x2 x3)).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) /\ (~ (x1 x2)).
Definition term102 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@UNION a0 (@INSERT a0 x0 x1) x2)) = (@IN a0 y0 (@INSERT a0 x0 (@UNION a0 x1 x2))).
Definition term81 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := and (((~ (x3 = x0)) /\ (~ (x1 x3))) /\ (~ (x2 x3))).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @COND (a0 -> Prop) (@IN a0 x0 x2) (@UNION a0 x1 x2) (@INSERT a0 x0 (@UNION a0 x1 x2)).
Definition term0 (a0 : Type') (x0 : type686 a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := x0 (@COND (a0 -> Prop) x1 x2 x3).
Definition term73 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := and (~ ((x2 = x0) \/ (x1 x2))).
Definition term156 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, (@UNION a0 (@INSERT a0 x0 x1) y0) = (@COND (a0 -> Prop) (@IN a0 x0 y0) (@UNION a0 x1 y0) (@INSERT a0 x0 (@UNION a0 x1 y0))).
Definition term90 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ ((~ (x1 x3)) /\ (~ (x2 x3)))) \/ ((((~ (x3 = x0)) /\ (~ (x1 x3))) /\ (~ (x2 x3))) /\ ((x1 x3) \/ (x2 x3))).
Definition term115 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (((~ ((~ (x2 x0)) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))))) -> False) -> (~ ((~ (x2 x0)) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))))) -> False) -> (~ ((~ (x2 x0)) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))))) -> False.
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (((~ ((x2 x0) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((x1 y0) \/ (x2 y0)))) -> False) -> (~ ((x2 x0) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((x1 y0) \/ (x2 y0)))) -> False) -> (~ ((x2 x0) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((x1 y0) \/ (x2 y0)))) -> False.
Definition term74 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := and ((~ (x2 = x0)) /\ (~ (x1 x2))).
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((x1 y0) \/ (x2 y0)).
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@UNION a0 (@INSERT a0 x0 x1) x2) = y0) (@COND (a0 -> Prop) (@IN a0 x0 x2) (@UNION a0 x1 x2) (@INSERT a0 x0 (@UNION a0 x1 x2))).
Definition term150 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (~ (x0 = x1)).
Definition term144 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term157 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@UNION a0 (@INSERT a0 x0 y0) y1) = (@COND (a0 -> Prop) (@IN a0 x0 y1) (@UNION a0 y0 y1) (@INSERT a0 x0 (@UNION a0 y0 y1))).
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := or (@IN a0 x0 (@INSERT a0 x1 x2)).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (x1 y0) -> forall y1 : a0, (((y1 = y0) \/ (x0 y1)) \/ (x1 y1)) = ((x0 y1) \/ (x1 y1)).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) \/ (x1 x2).
Definition term111 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ (x2 x0)) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))).
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop ((fun y0 : a0 -> Prop => (@UNION a0 (@INSERT a0 x0 x1) x2) = y0) (@COND (a0 -> Prop) (@IN a0 x0 x2) (@UNION a0 x1 x2) (@INSERT a0 x0 (@UNION a0 x1 x2)))).
Definition term141 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ ((~ (x3 = x0)) /\ ((~ (x1 x3)) /\ (~ (x2 x3))))).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (~ (x0 x1)).
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := and ((@IN a0 x0 x2) -> (fun y0 : a0 -> Prop => (@UNION a0 (@INSERT a0 x0 x1) x2) = y0) (@UNION a0 x1 x2)).
Definition term134 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (x3 = x0)) /\ ((~ (x1 x3)) /\ (~ (x2 x3))).
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : Prop) (x4 : a0 -> Prop) (x5 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@UNION a0 (@INSERT a0 x0 x1) x2) = y0) (@COND (a0 -> Prop) x3 x4 x5).
Definition term151 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term136 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (((x3 = x0) \/ (x1 x3)) \/ (x2 x3))) /\ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3))).
Definition term131 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) = ((x3 = x0) \/ ((x1 x3) \/ (x2 x3)))).
Definition term140 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ (~ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3))))).
Definition term145 (a0 : Type') (x0 : a0) := fun y0 : a0 => ~ (y0 = x0).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term122 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (~ ((~ (x0 y1)) -> forall y2 : a0, (((y2 = y1) \/ (y0 y2)) \/ (x0 y2)) = ((y2 = y1) \/ ((y0 y2) \/ (x0 y2))))) -> False.
Definition term60 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (~ ((x0 y1) -> forall y2 : a0, (((y2 = y1) \/ (y0 y2)) \/ (x0 y2)) = ((y0 y2) \/ (x0 y2)))) -> False.
Definition term155 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (~ ((~ (x1 y0)) -> forall y1 : a0, (((y1 = y0) \/ (x0 y1)) \/ (x1 y1)) = ((y1 = y0) \/ ((x0 y1) \/ (x1 y1))))) -> False) x2.
Definition term101 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (~ ((x1 y0) -> forall y1 : a0, (((y1 = y0) \/ (x0 y1)) \/ (x1 y1)) = ((x0 y1) \/ (x1 y1)))) -> False) x2.
Definition term123 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (~ (x0 y1)) -> forall y2 : a0, (((y2 = y1) \/ (y0 y2)) \/ (x0 y2)) = ((y2 = y1) \/ ((y0 y2) \/ (x0 y2))).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (x0 y1) -> forall y2 : a0, (((y2 = y1) \/ (y0 y2)) \/ (x0 y2)) = ((y0 y2) \/ (x0 y2)).
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ((@IN a0 x0 x2) -> (@UNION a0 (@INSERT a0 x0 x1) x2) = (@UNION a0 x1 x2)) /\ ((~ (@IN a0 x0 x2)) -> (@UNION a0 (@INSERT a0 x0 x1) x2) = (@INSERT a0 x0 (@UNION a0 x1 x2))).
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> Prop) := (@IN a0 x2 (@INSERT a0 x0 x1)) \/ (@IN a0 x2 x3).
Definition term103 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ (@IN a0 x0 x2)) -> forall y0 : a0, (@IN a0 y0 (@UNION a0 (@INSERT a0 x0 x1) x2)) = (@IN a0 y0 (@INSERT a0 x0 (@UNION a0 x1 x2))).
Definition term80 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := and (~ (((x3 = x0) \/ (x1 x3)) \/ (x2 x3))).
Definition term77 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ (((x3 = x0) \/ (x1 x3)) \/ (x2 x3)).
Definition term109 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))).
Definition term108 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@UNION a0 (@INSERT a0 x0 x1) x2)) = (@IN a0 y0 (@INSERT a0 x0 (@UNION a0 x1 x2))).
Definition term154 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (~ ((~ (x0 y1)) -> forall y2 : a0, (((y2 = y1) \/ (y0 y2)) \/ (x0 y2)) = ((y2 = y1) \/ ((y0 y2) \/ (x0 y2))))) -> False) x1.
Definition term100 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (~ ((x0 y1) -> forall y2 : a0, (((y2 = y1) \/ (y0 y2)) \/ (x0 y2)) = ((y0 y2) \/ (x0 y2)))) -> False) x1.
Definition term127 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (~ (y0 y2)) -> forall y3 : a0, (((y3 = y2) \/ (y1 y3)) \/ (y0 y3)) = ((y3 = y2) \/ ((y1 y3) \/ (y0 y3))).
Definition term126 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (~ ((~ (y0 y2)) -> forall y3 : a0, (((y3 = y2) \/ (y1 y3)) \/ (y0 y3)) = ((y3 = y2) \/ ((y1 y3) \/ (y0 y3))))) -> False.
Definition term65 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (y0 y2) -> forall y3 : a0, (((y3 = y2) \/ (y1 y3)) \/ (y0 y3)) = ((y1 y3) \/ (y0 y3)).
Definition term64 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (~ ((y0 y2) -> forall y3 : a0, (((y3 = y2) \/ (y1 y3)) \/ (y0 y3)) = ((y1 y3) \/ (y0 y3)))) -> False.
Definition term113 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ~ ((~ (x2 x0)) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0)))).
Definition term25 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@UNION a0 (@INSERT a0 x0 x1) x2)) = (@IN a0 y0 (@UNION a0 x1 x2)).
Definition term116 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (((~ ((~ (x2 x0)) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))))) -> False) -> (~ ((~ (x2 x0)) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))))) -> False) -> ((~ ((~ (x2 x0)) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))))) -> False) -> (~ ((~ (x2 x0)) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))))) -> False.
Definition term53 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (((~ ((x2 x0) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((x1 y0) \/ (x2 y0)))) -> False) -> (~ ((x2 x0) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((x1 y0) \/ (x2 y0)))) -> False) -> ((~ ((x2 x0) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((x1 y0) \/ (x2 y0)))) -> False) -> (~ ((x2 x0) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((x1 y0) \/ (x2 y0)))) -> False.
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @UNION a0 (@INSERT a0 x0 x1) x2.
Definition term41 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := or (@IN a0 x0 x1).
Definition term112 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ ((~ (x2 x0)) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((y0 = x0) \/ ((x1 y0) \/ (x2 y0))))) -> False.
Definition term49 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ ((x2 x0) -> forall y0 : a0, (((y0 = x0) \/ (x1 y0)) \/ (x2 y0)) = ((x1 y0) \/ (x2 y0)))) -> False.
Definition term133 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (x3 = x0)) /\ (~ ((x1 x3) \/ (x2 x3))).
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ (@IN a0 x0 x2)) -> (fun y0 : a0 -> Prop => (@UNION a0 (@INSERT a0 x0 x1) x2) = y0) (@INSERT a0 x0 (@UNION a0 x1 x2)).
Definition term107 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (x3 = x0) \/ ((x1 x3) \/ (x2 x3)).
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop ((@UNION a0 (@INSERT a0 x0 x1) x2) = (@COND (a0 -> Prop) (@IN a0 x0 x2) (@UNION a0 x1 x2) (@INSERT a0 x0 (@UNION a0 x1 x2)))).
Definition term138 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ (~ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3)))).
Definition term75 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ ((x3 = x0) \/ (x1 x3))) /\ (~ (x2 x3)).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term152 (a0 : Type') (x0 : a0) := (x0 = x0) -> False.
Definition term40 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop (((x3 = x0) \/ (x1 x3)) \/ (x2 x3)).
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := or ((x2 = x0) \/ (x1 x2)).
Definition term85 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ (~ ((x1 x3) \/ (x2 x3))).
Definition term125 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (~ (x0 y1)) -> forall y2 : a0, (((y2 = y1) \/ (y0 y2)) \/ (x0 y2)) = ((y2 = y1) \/ ((y0 y2) \/ (x0 y2))).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (x0 y1) -> forall y2 : a0, (((y2 = y1) \/ (y0 y2)) \/ (x0 y2)) = ((y0 y2) \/ (x0 y2)).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (~ (x1 y0)) -> forall y1 : a0, (((y1 = y0) \/ (x0 y1)) \/ (x1 y1)) = ((y1 = y0) \/ ((x0 y1) \/ (x1 y1))).
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@UNION a0 (@INSERT a0 x0 x1) x2) = y0) (@INSERT a0 x0 (@UNION a0 x1 x2)).
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @INSERT a0 x0 (@UNION a0 x1 x2).
Definition term147 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x0.
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (x0 x1).
Definition term142 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((((x3 = x0) \/ (x1 x3)) \/ (x2 x3)) /\ (~ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3))))) \/ ((~ (((x3 = x0) \/ (x1 x3)) \/ (x2 x3))) /\ ((x3 = x0) \/ ((x1 x3) \/ (x2 x3)))).
