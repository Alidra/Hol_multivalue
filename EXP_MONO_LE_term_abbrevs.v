Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ ((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0))))).
Definition term131 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term178 := (~ False) -> False.
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := (((Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term123 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term100 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (Peano.lt x0 x1)) \/ (x2 = (NUMERAL 0))) \/ (Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term158 (x0 : Prop) := ~ (~ x0).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) /\ (~ (x2 = (NUMERAL 0))).
Definition term179 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.pow y2 y0) (Nat.pow y1 y0)) -> (~ ((Peano.le y2 y1) \/ (y0 = (NUMERAL 0)))) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y3 y4) /\ (~ (y5 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y3 y5) (Nat.pow y4 y5)) -> (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) = (Peano.lt y4 y3)) -> False) x0.
Definition term143 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.lt y0 y1)) \/ (y2 = (NUMERAL 0))) \/ (Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2))) x0.
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 y1) -> Peano.le (Nat.pow y0 y2) (Nat.pow y1 y2)) x0.
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (Peano.lt x0 x1)) \/ (x2 = (NUMERAL 0))).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x0 x1) -> Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) x2.
Definition term79 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (Peano.lt x0 x1)) \/ (y0 = (NUMERAL 0))) \/ (Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)).
Definition term172 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((~ (x2 = (NUMERAL 0))) /\ (~ (Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)))).
Definition term109 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term67 (x0 : nat) (x1 : nat) := or (~ (Peano.lt x0 x1)).
Definition term173 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x0 = (NUMERAL 0))) /\ (~ (Peano.lt (Nat.pow x1 x0) (Nat.pow x2 x0)))) -> ~ (Peano.lt x1 x2).
Definition term55 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term24 (x0 : Prop) := (~ x0) -> False.
Definition term124 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term101 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ (forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term142 := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term93 (x0 : nat) := forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0)))) -> False.
Definition term118 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0.
Definition term113 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0.
Definition term105 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1)).
Definition term107 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0)) x1.
Definition term145 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ (Peano.lt x0 x1)) \/ (y0 = (NUMERAL 0))) \/ (Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0))) x2.
Definition term156 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term98 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term121 := fun y0 : nat => (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term32 := ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term184 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (Peano.le x0 x1) \/ (x2 = (NUMERAL 0))) /\ (((Peano.le x0 x1) \/ (x2 = (NUMERAL 0))) -> Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term164 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)) -> ~ (Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term160 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term152 (x0 : Prop) := (~ x0) -> x0.
Definition term155 (x0 : nat) (x1 : nat) := @eq Prop ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1))).
Definition term154 (x0 : nat) (x1 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2).
Definition term168 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term19 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term150 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2))) -> Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2).
Definition term176 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> Peano.le x0 x1.
Definition term59 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2).
Definition term102 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0)).
Definition term92 (x0 : nat) := fun y0 : nat => ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term133 := @eq Prop (forall y0 : nat, (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0))).
Definition term132 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0)).
Definition term111 (x0 : nat) := @eq Prop (forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0))).
Definition term110 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0)).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))).
Definition term169 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((x2 = (NUMERAL 0)) \/ (Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2))).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term35 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term185 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) = ((Peano.le x0 x1) \/ (y0 = (NUMERAL 0))).
Definition term180 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.pow y1 x0) (Nat.pow y0 x0)) -> (~ ((Peano.le y1 y0) \/ (x0 = (NUMERAL 0)))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y2 y3) /\ (~ (y4 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y2 y4) (Nat.pow y3 y4)) -> (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)) -> False) x1.
Definition term144 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (Peano.lt x0 y0)) \/ (y1 = (NUMERAL 0))) \/ (Peano.lt (Nat.pow x0 y1) (Nat.pow y0 y1))) x1.
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le x0 y0) -> Peano.le (Nat.pow x0 y1) (Nat.pow y0 y1)) x1.
Definition term175 (x0 : nat) (x1 : nat) := (~ (Peano.lt x1 x0)) -> Peano.le x0 x1.
Definition term90 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))) /\ ((~ (~ (Peano.le x1 x0))) \/ (Peano.lt x0 x1)).
Definition term71 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term182 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0))) -> Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2).
Definition term43 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le (Nat.pow y0 x1) (Nat.pow x0 x1)) -> (~ ((Peano.le y0 x0) \/ (x1 = (NUMERAL 0)))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (~ (y3 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y1 y3) (Nat.pow y2 y3)) -> ~ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)).
Definition term126 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0).
Definition term57 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2).
Definition term119 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.lt y0 x0).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term153 (x0 : nat) (x1 : nat) := (~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1)).
Definition term87 (x0 : nat) (x1 : nat) := (~ (~ (Peano.le x1 x0))) \/ (Peano.lt x0 x1).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0)))).
Definition term16 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term54 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term112 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0.
Definition term86 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term12 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 x1) -> Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0).
Definition term31 := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := (((Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> ((Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term116 (x0 : nat) := and (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))).
Definition term18 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) x0.
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term167 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term187 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.pow y0 y2) (Nat.pow y1 y2)) = ((Peano.le y0 y1) \/ (y2 = (NUMERAL 0))).
Definition term186 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.pow x0 y1) (Nat.pow y0 y1)) = ((Peano.le x0 y0) \/ (y1 = (NUMERAL 0))).
Definition term141 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0).
Definition term136 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0)).
Definition term95 := forall y0 : nat, forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ ((Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term83 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (Peano.lt y0 y1)) \/ (y2 = (NUMERAL 0))) \/ (Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)).
Definition term81 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (Peano.lt x0 y0)) \/ (y1 = (NUMERAL 0))) \/ (Peano.lt (Nat.pow x0 y1) (Nat.pow y0 y1)).
Definition term64 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2).
Definition term62 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow y0 y1).
Definition term53 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.pow y2 y0) (Nat.pow y1 y0)) -> (~ ((Peano.le y2 y1) \/ (y0 = (NUMERAL 0)))) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y3 y4) /\ (~ (y5 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y3 y5) (Nat.pow y4 y5)) -> ~ (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) = (Peano.lt y4 y3)).
Definition term52 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.pow y2 y0) (Nat.pow y1 y0)) -> (~ ((Peano.le y2 y1) \/ (y0 = (NUMERAL 0)))) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y3 y4) /\ (~ (y5 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y3 y5) (Nat.pow y4 y5)) -> (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) = (Peano.lt y4 y3)) -> False.
Definition term49 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.pow y1 x0) (Nat.pow y0 x0)) -> (~ ((Peano.le y1 y0) \/ (x0 = (NUMERAL 0)))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y2 y3) /\ (~ (y4 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y2 y4) (Nat.pow y3 y4)) -> ~ (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)).
Definition term48 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.pow y1 x0) (Nat.pow y0 x0)) -> (~ ((Peano.le y1 y0) \/ (x0 = (NUMERAL 0)))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y2 y3) /\ (~ (y4 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y2 y4) (Nat.pow y3 y4)) -> (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)) -> False.
Definition term33 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term10 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 y0) -> Peano.le (Nat.pow x0 y1) (Nat.pow y0 y1).
Definition term130 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0) /\ ((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)) x0).
Definition term157 (x0 : nat) (x1 : nat) := (~ (~ (Peano.le x1 x0))) -> ~ (Peano.lt x0 x1).
Definition term56 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term89 (x0 : nat) (x1 : nat) := and ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))).
Definition term181 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.pow y0 x1) (Nat.pow x0 x1)) -> (~ ((Peano.le y0 x0) \/ (x1 = (NUMERAL 0)))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (~ (y3 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y1 y3) (Nat.pow y2 y3)) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)) -> False) x2.
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x1)) \/ ((x2 = (NUMERAL 0)) \/ (Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2))).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) -> Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term161 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> ~ (Peano.lt x0 x1).
Definition term163 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term88 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.lt x0 x1).
Definition term42 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le (Nat.pow y0 x1) (Nat.pow x0 x1)) -> (~ ((Peano.le y0 x0) \/ (x1 = (NUMERAL 0)))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (~ (y3 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y1 y3) (Nat.pow y2 y3)) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)) -> False.
Definition term108 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1) /\ ((fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0)) x1).
Definition term99 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term148 (x0 : nat) := (x0 = (NUMERAL 0)) -> ~ (x0 = (NUMERAL 0)).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0))).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x1)) \/ (x2 = (NUMERAL 0)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x1)) \/ (~ (~ (x2 = (NUMERAL 0)))).
Definition term120 (x0 : nat) := (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ (forall y0 : nat, (Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term138 := and (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) -> (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) = True.
Definition term147 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term139 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0.
Definition term134 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0.
Definition term165 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((x0 = (NUMERAL 0)) \/ (Peano.lt (Nat.pow x1 x0) (Nat.pow x2 x0)))) -> ~ (Peano.lt x1 x2).
Definition term129 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)) x0.
Definition term127 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0.
Definition term17 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term84 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term21 (x0 : nat) (x1 : nat) := Peano.le (Nat.pow x0 x1).
Definition term60 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0).
Definition term151 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term78 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (Peano.lt x0 x1)) \/ (y0 = (NUMERAL 0))) \/ (Peano.lt (Nat.pow x0 y0) (Nat.pow x1 y0)).
Definition term103 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0).
Definition term114 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0)).
Definition term162 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.pow x1 x2) (Nat.pow x0 x2)) -> ~ (Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0))).
Definition term171 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((x2 = (NUMERAL 0)) \/ (Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)))).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0))))) \/ (Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term183 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (Peano.le x0 x1) \/ (x2 = (NUMERAL 0)).
Definition term117 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0.
Definition term36 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term137 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0).
Definition term115 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0).
Definition term128 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := imp (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term85 (x0 : nat) (x1 : nat) := or (~ (~ (Peano.le x0 x1))).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) \/ (x2 = (NUMERAL 0)).
Definition term125 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0)).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term122 := forall y0 : nat, (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term45 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.pow y0 x1) (Nat.pow x0 x1)) -> (~ ((Peano.le y0 x0) \/ (x1 = (NUMERAL 0)))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (~ (y3 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y1 y3) (Nat.pow y2 y3)) -> ~ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)).
Definition term44 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.pow y0 x1) (Nat.pow x0 x1)) -> (~ ((Peano.le y0 x0) \/ (x1 = (NUMERAL 0)))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (~ (y3 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y1 y3) (Nat.pow y2 y3)) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)) -> False.
Definition term106 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)) -> (~ ((Peano.le x0 x1) \/ (x2 = (NUMERAL 0)))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term91 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))) /\ ((Peano.le x1 x0) \/ (Peano.lt x0 x1)).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term66 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term166 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = (NUMERAL 0)) \/ (Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term170 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = (NUMERAL 0))) /\ (~ (Peano.lt (Nat.pow x0 x2) (Nat.pow x1 x2))).
Definition term23 := Peano.le (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term174 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> ~ (Peano.lt x0 x1).
Definition term140 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0.
Definition term135 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0.
Definition term34 := imp (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)).
Definition term177 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> False.
Definition term104 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1.
Definition term94 := fun y0 : nat => forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ ((Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term80 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((~ (Peano.lt x0 y0)) \/ (y1 = (NUMERAL 0))) \/ (Peano.lt (Nat.pow x0 y1) (Nat.pow y0 y1)).
Definition term61 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (~ (y1 = (NUMERAL 0)))) -> Peano.lt (Nat.pow x0 y1) (Nat.pow y0 y1).
Definition term47 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.pow y1 x0) (Nat.pow y0 x0)) -> (~ ((Peano.le y1 y0) \/ (x0 = (NUMERAL 0)))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y2 y3) /\ (~ (y4 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y2 y4) (Nat.pow y3 y4)) -> ~ (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)).
Definition term46 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.pow y1 x0) (Nat.pow y0 x0)) -> (~ ((Peano.le y1 y0) \/ (x0 = (NUMERAL 0)))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y2 y3) /\ (~ (y4 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y2 y4) (Nat.pow y3 y4)) -> (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)) -> False.
Definition term20 := NUMERAL (BIT1 0).
Definition term22 := Peano.le (NUMERAL (BIT1 0)).
Definition term149 (x0 : Prop) := x0 -> ~ x0.
Definition term82 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.lt y0 y1)) \/ (y2 = (NUMERAL 0))) \/ (Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2)).
Definition term63 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y0 y2) (Nat.pow y1 y2).
Definition term51 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.pow y2 y0) (Nat.pow y1 y0)) -> (~ ((Peano.le y2 y1) \/ (y0 = (NUMERAL 0)))) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y3 y4) /\ (~ (y5 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y3 y5) (Nat.pow y4 y5)) -> ~ (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) = (Peano.lt y4 y3)).
Definition term50 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.pow y2 y0) (Nat.pow y1 y0)) -> (~ ((Peano.le y2 y1) \/ (y0 = (NUMERAL 0)))) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y3 y4) /\ (~ (y5 = (NUMERAL 0)))) -> Peano.lt (Nat.pow y3 y5) (Nat.pow y4 y5)) -> (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) = (Peano.lt y4 y3)) -> False.
Definition term159 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.le x0 x1))).
