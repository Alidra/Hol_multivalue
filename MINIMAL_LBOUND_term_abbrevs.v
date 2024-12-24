Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term102 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (fun y1 : nat => (x1 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 x0)) \/ (~ (x1 y2)))) y0.
Definition term51 (x0 : nat -> Prop) := fun y0 : nat => x0 y0.
Definition term183 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0).
Definition term82 (x0 : type993) := ~ (all x0).
Definition term61 (x0 : nat -> Prop) := ~ (all x0).
Definition term128 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := fun y0 : nat => ((x1 x0) /\ (forall y1 : nat, (~ (Peano.lt y1 x2)) \/ (~ (x1 y1)))) /\ ((x1 y0) /\ (~ (Peano.le x2 y0))).
Definition term214 := (~ False) -> False.
Definition term33 := (~ (forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False.
Definition term97 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 x1)) \/ (~ (x0 y2)))) y0) /\ (exists y0 : nat, (x0 y0) /\ (~ (Peano.le x1 y0))).
Definition term55 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 x1).
Definition term155 (x0 : nat) := fun y0 : nat => (Peano.lt x0 y0) \/ (Peano.le y0 x0).
Definition term107 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := and ((fun y0 : nat => (x1 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 x0)) \/ (~ (x1 y1)))) x2).
Definition term2 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, x0 y1) -> (Peano.le y0 (minimal x0)) = (forall y1 : nat, (x0 y1) -> Peano.le y0 y1)) x1.
Definition term87 := fun y0 : nat -> Prop => ~ ((fun y1 : nat -> Prop => forall y2 : nat, ((exists y3 : nat, y1 y3) /\ (forall y3 : nat, (Peano.lt y3 y2) -> ~ (y1 y3))) -> forall y3 : nat, (y1 y3) -> Peano.le y2 y3) y0).
Definition term52 (x0 : nat -> Prop) := and (exists y0 : nat, x0 y0).
Definition term175 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0).
Definition term152 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ ((fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0).
Definition term89 := exists y0 : nat -> Prop, exists y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (y0 y2)))) /\ (exists y2 : nat, (y0 y2) /\ (~ (Peano.le y1 y2))).
Definition term202 (x0 : Prop) := ~ (~ x0).
Definition term98 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 x1)) \/ (~ (x0 y2)))) y0) /\ (exists y1 : nat, (x0 y1) /\ (~ (Peano.le x1 y1))).
Definition term84 := exists y0 : nat -> Prop, ~ ((fun y1 : nat -> Prop => forall y2 : nat, ((exists y3 : nat, y1 y3) /\ (forall y3 : nat, (Peano.lt y3 y2) -> ~ (y1 y3))) -> forall y3 : nat, (y1 y3) -> Peano.le y2 y3) y0).
Definition term161 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ ((fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0).
Definition term196 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (~ (Peano.lt y0 x0)) \/ (~ (x1 y0))) x2.
Definition term130 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => exists y1 : nat, ((x0 y0) /\ (forall y2 : nat, (~ (Peano.lt y2 x1)) \/ (~ (x0 y2)))) /\ ((x0 y1) /\ (~ (Peano.le x1 y1))).
Definition term19 (x0 : nat -> Prop) (x1 : nat) := (((exists y0 : nat, x0 y0) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0)) -> (((exists y0 : nat, x0 y0) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0))) -> Peano.le x1 (minimal x0)) = (((exists y0 : nat, x0 y0) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0))) -> forall y0 : nat, (x0 y0) -> Peano.le x1 y0).
Definition term108 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := and ((x2 x0) /\ (forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x2 y0)))).
Definition term115 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term30 (x0 : Prop) := (~ x0) -> False.
Definition term77 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => ((exists y1 : nat, x0 y1) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> forall y1 : nat, (x0 y1) -> Peano.le y0 y1) x1.
Definition term176 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0).
Definition term153 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ (forall y0 : nat, (fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0).
Definition term194 := (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term145 (x0 : nat) := forall y0 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ ((Peano.lt x0 y0) \/ (Peano.le y0 x0)).
Definition term119 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := exists y0 : nat, ((x1 x0) /\ (forall y1 : nat, (~ (Peano.lt y1 x2)) \/ (~ (x1 y1)))) /\ ((fun y1 : nat => (x1 y1) /\ (~ (Peano.le x2 y1))) y0).
Definition term58 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, x1 y0) /\ (forall y0 : nat, (~ (Peano.lt y0 x0)) \/ (~ (x1 y0))).
Definition term11 (x0 : nat) (x1 : nat -> Prop) := (exists y0 : nat, x1 y0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0)).
Definition term88 := fun y0 : nat -> Prop => exists y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (~ (Peano.lt y2 y1)) \/ (~ (y0 y2)))) /\ (exists y2 : nat, (y0 y2) /\ (~ (Peano.le y1 y2))).
Definition term143 (x0 : nat) (x1 : nat) := ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1))) /\ ((Peano.lt x1 x0) \/ (Peano.le x0 x1)).
Definition term46 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x2) -> Peano.le x1 x2.
Definition term111 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 x1)) \/ (~ (x0 y2)))) y0) /\ (exists y1 : nat, (x0 y1) /\ (~ (Peano.le x1 y1))).
Definition term170 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0.
Definition term165 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0.
Definition term205 (x0 : nat -> Prop) (x1 : nat) := imp (x0 x1).
Definition term159 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) \/ (Peano.le y0 x0)) x1.
Definition term125 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := ((x1 x0) /\ (forall y0 : nat, (~ (Peano.lt y0 x2)) \/ (~ (x1 y0)))) /\ ((fun y0 : nat => (x1 y0) /\ (~ (Peano.le x2 y0))) x3).
Definition term200 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term150 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term65 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 y0) -> Peano.le x1 y0) x2.
Definition term75 (x0 : nat -> Prop) := ~ (forall y0 : nat, ((exists y1 : nat, x0 y1) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> forall y1 : nat, (x0 y1) -> Peano.le y0 y1).
Definition term63 (x0 : nat -> Prop) (x1 : nat) := ~ (forall y0 : nat, (x0 y0) -> Peano.le x1 y0).
Definition term173 := fun y0 : nat => (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term38 := ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)).
Definition term135 := exists y0 : nat -> Prop, exists y1 : nat, exists y2 : nat, exists y3 : nat, ((y0 y2) /\ (forall y4 : nat, (~ (Peano.lt y4 y1)) \/ (~ (y0 y4)))) /\ ((y0 y3) /\ (~ (Peano.le y1 y3))).
Definition term114 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term32 := ~ (forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2).
Definition term120 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 y0) /\ (~ (Peano.le x1 y0))) x2.
Definition term25 (x0 : nat -> Prop) := forall y0 : nat, ((exists y1 : nat, x0 y1) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> forall y1 : nat, (x0 y1) -> Peano.le y0 y1.
Definition term199 (x0 : Prop) := (~ x0) -> x0.
Definition term206 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x1) -> ~ (Peano.lt x1 x2).
Definition term212 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> Peano.le x0 x1.
Definition term68 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (x0 y0) /\ (~ (Peano.le x1 y0)).
Definition term104 (x0 : nat) (x1 : nat -> Prop) := and (exists y0 : nat, (fun y1 : nat => (x1 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 x0)) \/ (~ (x1 y2)))) y0).
Definition term154 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0)).
Definition term144 (x0 : nat) := fun y0 : nat => ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ ((Peano.lt x0 y0) \/ (Peano.le y0 x0)).
Definition term185 := @eq Prop (forall y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0))).
Definition term184 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0)).
Definition term163 (x0 : nat) := @eq Prop (forall y0 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ ((Peano.lt x0 y0) \/ (Peano.le y0 x0))).
Definition term162 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0) /\ ((fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0)).
Definition term149 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term71 (x0 : nat) (x1 : nat -> Prop) := and ((exists y0 : nat, x1 y0) /\ (forall y0 : nat, (~ (Peano.lt y0 x0)) \/ (~ (x1 y0)))).
Definition term70 (x0 : nat) (x1 : nat -> Prop) := and ((exists y0 : nat, x1 y0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))).
Definition term211 (x0 : nat) (x1 : nat) := (~ (Peano.lt x1 x0)) -> Peano.le x0 x1.
Definition term109 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((fun y0 : nat => (x1 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 x2)) \/ (~ (x1 y1)))) x0) /\ (exists y0 : nat, (x1 y0) /\ (~ (Peano.le x2 y0))).
Definition term178 := fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0).
Definition term45 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term136 (x0 : nat) (x1 : nat) := ~ (~ (Peano.lt x0 x1)).
Definition term171 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) \/ (Peano.le y0 x0).
Definition term99 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (x1 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 x0)) \/ (~ (x1 y1))).
Definition term80 (x0 : nat -> Prop) := fun y0 : nat => ((exists y1 : nat, x0 y1) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (exists y1 : nat, (x0 y1) /\ (~ (Peano.le y0 y1))).
Definition term157 (x0 : nat) (x1 : nat) := (~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1)).
Definition term117 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term22 (x0 : nat -> Prop) := fun y0 : nat => ((exists y1 : nat, x0 y1) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> Peano.le y0 (minimal x0).
Definition term4 (x0 : nat -> Prop) := exists y0 : nat, x0 y0.
Definition term7 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term198 (x0 : nat -> Prop) (x1 : nat) := (~ (x0 x1)) -> x0 x1.
Definition term197 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term164 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0.
Definition term138 (x0 : nat) (x1 : nat) := or (Peano.lt x0 x1).
Definition term116 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term56 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (~ (Peano.lt y0 x0)) \/ (~ (x1 y0)).
Definition term106 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1)))) /\ (exists y0 : nat, (x0 y0) /\ (~ (Peano.le x1 y0)))).
Definition term105 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (x0 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 x1)) \/ (~ (x0 y2)))) y0) /\ (exists y0 : nat, (x0 y0) /\ (~ (Peano.le x1 y0)))).
Definition term86 (x0 : nat -> Prop) := ~ ((fun y0 : nat -> Prop => forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2) x0).
Definition term37 := (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False.
Definition term49 (x0 : nat) (x1 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 x0) -> ~ (x1 y0).
Definition term121 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (x0 y1) /\ (~ (Peano.le x1 y1))) y0.
Definition term110 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((x1 x0) /\ (forall y0 : nat, (~ (Peano.lt y0 x2)) \/ (~ (x1 y0)))) /\ (exists y0 : nat, (x1 y0) /\ (~ (Peano.le x2 y0))).
Definition term27 := fun y0 : nat -> Prop => forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2.
Definition term26 := fun y0 : nat -> Prop => forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> Peano.le y1 (minimal y0).
Definition term43 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term168 (x0 : nat) := and (forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))).
Definition term24 (x0 : nat -> Prop) := forall y0 : nat, ((exists y1 : nat, x0 y1) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> Peano.le y0 (minimal x0).
Definition term35 := (((~ (forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False) -> (~ (forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False) -> (~ (forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False.
Definition term127 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := fun y0 : nat => ((x1 x0) /\ (forall y1 : nat, (~ (Peano.lt y1 x2)) \/ (~ (x1 y1)))) /\ ((fun y1 : nat => (x1 y1) /\ (~ (Peano.le x2 y1))) y0).
Definition term204 (x0 : nat -> Prop) (x1 : nat) := imp (~ (~ (x0 x1))).
Definition term48 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.lt x2 x0) -> ~ (x1 x2).
Definition term193 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0).
Definition term188 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0)).
Definition term147 := forall y0 : nat, forall y1 : nat, ((~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ ((Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term39 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term113 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1)))) /\ (exists y1 : nat, (x0 y1) /\ (~ (Peano.le x1 y1))).
Definition term81 (x0 : nat -> Prop) := exists y0 : nat, ((exists y1 : nat, x0 y1) /\ (forall y1 : nat, (~ (Peano.lt y1 y0)) \/ (~ (x0 y1)))) /\ (exists y1 : nat, (x0 y1) /\ (~ (Peano.le y0 y1))).
Definition term6 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (x0 y0) -> Peano.le x1 y0.
Definition term66 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => (x0 y0) -> Peano.le x1 y0) x2).
Definition term182 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) x0) /\ ((fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) x0).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term44 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term132 (x0 : nat -> Prop) := fun y0 : nat => exists y1 : nat, exists y2 : nat, ((x0 y1) /\ (forall y3 : nat, (~ (Peano.lt y3 y0)) \/ (~ (x0 y3)))) /\ ((x0 y2) /\ (~ (Peano.le y0 y2))).
Definition term14 (x0 : nat) (x1 : nat -> Prop) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => (((exists y1 : nat, x1 y1) /\ (forall y1 : nat, (Peano.lt y1 x0) -> ~ (x1 y1))) = x2) -> (x2 -> (Peano.le x0 (minimal x1)) = y0) -> (((exists y1 : nat, x1 y1) /\ (forall y1 : nat, (Peano.lt y1 x0) -> ~ (x1 y1))) -> Peano.le x0 (minimal x1)) = (x2 -> y0)) x3.
Definition term139 (x0 : nat) (x1 : nat) := (~ (~ (Peano.lt x1 x0))) \/ (Peano.le x0 x1).
Definition term141 (x0 : nat) (x1 : nat) := and ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1))).
Definition term72 (x0 : nat -> Prop) (x1 : nat) := ((exists y0 : nat, x0 y0) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0))) /\ (~ (forall y0 : nat, (x0 y0) -> Peano.le x1 y0)).
Definition term69 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (x0 y0) /\ (~ (Peano.le x1 y0)).
Definition term100 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (fun y0 : nat => (x1 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 x0)) \/ (~ (x1 y1)))) x2.
Definition term47 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (x0 y0) -> Peano.le x1 y0.
Definition term21 (x0 : nat -> Prop) (x1 : nat) := ((exists y0 : nat, x0 y0) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0))) -> forall y0 : nat, (x0 y0) -> Peano.le x1 y0.
Definition term93 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term31 := (~ (forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2)) -> False.
Definition term20 (x0 : nat) (x1 : nat -> Prop) := ((exists y0 : nat, x1 y0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))) -> Peano.le x0 (minimal x1).
Definition term209 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.lt x0 x1).
Definition term50 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0).
Definition term13 (x0 : nat) (x1 : nat -> Prop) (x2 : Prop) := forall y0 : Prop, (((exists y1 : nat, x1 y1) /\ (forall y1 : nat, (Peano.lt y1 x0) -> ~ (x1 y1))) = x2) -> (x2 -> (Peano.le x0 (minimal x1)) = y0) -> (((exists y1 : nat, x1 y1) /\ (forall y1 : nat, (Peano.lt y1 x0) -> ~ (x1 y1))) -> Peano.le x0 (minimal x1)) = (x2 -> y0).
Definition term8 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term160 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) x1) /\ ((fun y0 : nat => (Peano.lt x0 y0) \/ (Peano.le y0 x0)) x1).
Definition term151 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term203 (x0 : nat -> Prop) (x1 : nat) := ~ (~ (x0 x1)).
Definition term122 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (x0 y1) /\ (~ (Peano.le x1 y1))) y0.
Definition term103 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (fun y1 : nat => (x1 y1) /\ (forall y2 : nat, (~ (Peano.lt y2 x0)) \/ (~ (x1 y2)))) y0.
Definition term124 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop (((x1 x0) /\ (forall y0 : nat, (~ (Peano.lt y0 x2)) \/ (~ (x1 y0)))) /\ (exists y0 : nat, (x1 y0) /\ (~ (Peano.le x2 y0)))).
Definition term123 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop (((x1 x0) /\ (forall y0 : nat, (~ (Peano.lt y0 x2)) \/ (~ (x1 y0)))) /\ (exists y0 : nat, (fun y1 : nat => (x1 y1) /\ (~ (Peano.le x2 y1))) y0)).
Definition term60 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x2) /\ (~ (Peano.le x1 x2)).
Definition term10 (x0 : nat) (x1 : nat -> Prop) := forall y0 : Prop, forall y1 : Prop, (((exists y2 : nat, x1 y2) /\ (forall y2 : nat, (Peano.lt y2 x0) -> ~ (x1 y2))) = y0) -> (y0 -> (Peano.le x0 (minimal x1)) = y1) -> (((exists y2 : nat, x1 y2) /\ (forall y2 : nat, (Peano.lt y2 x0) -> ~ (x1 y2))) -> Peano.le x0 (minimal x1)) = (y0 -> y1).
Definition term9 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term17 (x0 : nat) (x1 : nat -> Prop) (x2 : Prop) := (((exists y0 : nat, x1 y0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))) -> (Peano.le x0 (minimal x1)) = x2) -> (((exists y0 : nat, x1 y0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))) -> Peano.le x0 (minimal x1)) = (((exists y0 : nat, x1 y0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))) -> x2).
Definition term172 (x0 : nat) := (forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) /\ (forall y0 : nat, (Peano.lt x0 y0) \/ (Peano.le y0 x0)).
Definition term134 := fun y0 : nat -> Prop => exists y1 : nat, exists y2 : nat, exists y3 : nat, ((y0 y2) /\ (forall y4 : nat, (~ (Peano.lt y4 y1)) \/ (~ (y0 y4)))) /\ ((y0 y3) /\ (~ (Peano.le y1 y3))).
Definition term190 := and (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))).
Definition term5 (x0 : nat) (x1 : nat -> Prop) := Peano.le x0 (minimal x1).
Definition term42 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term29 := forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2.
Definition term28 := forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> Peano.le y1 (minimal y0).
Definition term92 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term129 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := exists y0 : nat, ((x1 x0) /\ (forall y1 : nat, (~ (Peano.lt y1 x2)) \/ (~ (x1 y1)))) /\ ((x1 y0) /\ (~ (Peano.le x2 y0))).
Definition term191 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0.
Definition term186 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0.
Definition term53 (x0 : nat) (x1 : nat -> Prop) := imp ((exists y0 : nat, x1 y0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))).
Definition term96 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, (x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1)))) /\ (exists y0 : nat, (x0 y0) /\ (~ (Peano.le x1 y0))).
Definition term181 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)) x0.
Definition term179 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) x0.
Definition term73 (x0 : nat -> Prop) (x1 : nat) := ((exists y0 : nat, x0 y0) /\ (forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x0 y0)))) /\ (exists y0 : nat, (x0 y0) /\ (~ (Peano.le x1 y0))).
Definition term23 (x0 : nat -> Prop) := fun y0 : nat => ((exists y1 : nat, x0 y1) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> forall y1 : nat, (x0 y1) -> Peano.le y0 y1.
Definition term95 (x0 : nat) (x1 : nat -> Prop) := and (exists y0 : nat, (x1 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 x0)) \/ (~ (x1 y1)))).
Definition term15 (x0 : nat) (x1 : nat -> Prop) (x2 : Prop) (x3 : Prop) := (((exists y0 : nat, x1 y0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))) = x2) -> (x2 -> (Peano.le x0 (minimal x1)) = x3) -> (((exists y0 : nat, x1 y0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))) -> Peano.le x0 (minimal x1)) = (x2 -> x3).
Definition term166 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0)).
Definition term76 (x0 : nat -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => ((exists y2 : nat, x0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) -> forall y2 : nat, (x0 y2) -> Peano.le y1 y2) y0).
Definition term64 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (x0 y1) -> Peano.le x1 y1) y0).
Definition term210 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.lt x1 x0) \/ (Peano.le x0 x1)).
Definition term112 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((x0 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 x1)) \/ (~ (x0 y1)))) /\ (exists y1 : nat, (x0 y1) /\ (~ (Peano.le x1 y1))).
Definition term41 := (~ (forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)).
Definition term169 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt x0 y1) \/ (Peano.le y1 x0)) y0.
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (x2 x0) /\ (forall y0 : nat, (~ (Peano.lt y0 x1)) \/ (~ (x2 y0))).
Definition term189 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0).
Definition term167 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (~ (Peano.lt x0 y1)) \/ (~ (Peano.le y1 x0))) y0).
Definition term180 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) x0).
Definition term142 (x0 : nat) (x1 : nat) := ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x1))) /\ ((~ (~ (Peano.lt x1 x0))) \/ (Peano.le x0 x1)).
Definition term201 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (~ (x0 x1))) -> ~ (Peano.lt x1 x2).
Definition term18 (x0 : nat -> Prop) (x1 : nat) := ((exists y0 : nat, x0 y0) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0).
Definition term1 (x0 : nat -> Prop) := forall y0 : nat, (exists y1 : nat, x0 y1) -> (Peano.le y0 (minimal x0)) = (forall y1 : nat, (x0 y1) -> Peano.le y0 y1).
Definition term137 (x0 : nat) (x1 : nat) := or (~ (~ (Peano.lt x0 x1))).
Definition term177 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0)).
Definition term94 (x0 : nat) (x1 : nat -> Prop) := exists y0 : nat, (x1 y0) /\ (forall y1 : nat, (~ (Peano.lt y1 x0)) \/ (~ (x1 y1))).
Definition term148 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term133 (x0 : nat -> Prop) := exists y0 : nat, exists y1 : nat, exists y2 : nat, ((x0 y1) /\ (forall y3 : nat, (~ (Peano.lt y3 y0)) \/ (~ (x0 y3)))) /\ ((x0 y2) /\ (~ (Peano.le y0 y2))).
Definition term131 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, exists y1 : nat, ((x0 y0) /\ (forall y2 : nat, (~ (Peano.lt y2 x1)) \/ (~ (x0 y2)))) /\ ((x0 y1) /\ (~ (Peano.le x1 y1))).
Definition term174 := forall y0 : nat, (forall y1 : nat, (~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ (forall y1 : nat, (Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term85 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2) x0.
Definition term0 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => forall y1 : nat, (exists y2 : nat, y0 y2) -> (Peano.le y1 (minimal y0)) = (forall y2 : nat, (y0 y2) -> Peano.le y1 y2)) x0.
Definition term195 (x0 : nat -> Prop) (x1 : nat) := and (x0 x1).
Definition term83 (x0 : type993) := exists y0 : nat -> Prop, ~ (x0 y0).
Definition term158 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) x1).
Definition term79 (x0 : nat -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => ((exists y2 : nat, x0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (x0 y2))) -> forall y2 : nat, (x0 y2) -> Peano.le y1 y2) y0).
Definition term67 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (x0 y1) -> Peano.le x1 y1) y0).
Definition term78 (x0 : nat -> Prop) (x1 : nat) := ~ ((fun y0 : nat => ((exists y1 : nat, x0 y1) /\ (forall y1 : nat, (Peano.lt y1 y0) -> ~ (x0 y1))) -> forall y1 : nat, (x0 y1) -> Peano.le y0 y1) x1).
Definition term16 (x0 : nat) (x1 : nat -> Prop) (x2 : Prop) := (((exists y0 : nat, x1 y0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))) = ((exists y0 : nat, x1 y0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0)))) -> (((exists y0 : nat, x1 y0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))) -> (Peano.le x0 (minimal x1)) = x2) -> (((exists y0 : nat, x1 y0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))) -> Peano.le x0 (minimal x1)) = (((exists y0 : nat, x1 y0) /\ (forall y0 : nat, (Peano.lt y0 x0) -> ~ (x1 y0))) -> x2).
Definition term126 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) (x3 : nat) := ((x1 x0) /\ (forall y0 : nat, (~ (Peano.lt y0 x2)) \/ (~ (x1 y0)))) /\ ((x1 x3) /\ (~ (Peano.le x2 x3))).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term34 := ((~ (forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False) -> (~ (forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False.
Definition term54 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (~ (Peano.lt x2 x0)) \/ (~ (x1 x2)).
Definition term36 := (((~ (forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False) -> (~ (forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False) -> ((~ (forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False) -> (~ (forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2)) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0)) -> False.
Definition term207 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> ~ (Peano.lt x0 x1).
Definition term192 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.lt y1 y2) \/ (Peano.le y2 y1)) y0.
Definition term187 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.lt y1 y2)) \/ (~ (Peano.le y2 y1))) y0.
Definition term59 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ~ ((x0 x2) -> Peano.le x1 x2).
Definition term213 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> False.
Definition term12 (x0 : nat) (x1 : nat -> Prop) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((exists y2 : nat, x1 y2) /\ (forall y2 : nat, (Peano.lt y2 x0) -> ~ (x1 y2))) = y0) -> (y0 -> (Peano.le x0 (minimal x1)) = y1) -> (((exists y2 : nat, x1 y2) /\ (forall y2 : nat, (Peano.lt y2 x0) -> ~ (x1 y2))) -> Peano.le x0 (minimal x1)) = (y0 -> y1)) x2.
Definition term62 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term118 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((x1 x0) /\ (forall y0 : nat, (~ (Peano.lt y0 x2)) \/ (~ (x1 y0)))) /\ (exists y0 : nat, (fun y1 : nat => (x1 y1) /\ (~ (Peano.le x2 y1))) y0).
Definition term74 (x0 : nat -> Prop) (x1 : nat) := ~ (((exists y0 : nat, x0 y0) /\ (forall y0 : nat, (Peano.lt y0 x1) -> ~ (x0 y0))) -> forall y0 : nat, (x0 y0) -> Peano.le x1 y0).
Definition term3 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, x0 y0) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0).
Definition term156 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 x0))) x1.
Definition term146 := fun y0 : nat => forall y1 : nat, ((~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y0))) /\ ((Peano.lt y0 y1) \/ (Peano.le y1 y0)).
Definition term40 := imp (~ (forall y0 : nat -> Prop, forall y1 : nat, ((exists y2 : nat, y0 y2) /\ (forall y2 : nat, (Peano.lt y2 y1) -> ~ (y0 y2))) -> forall y2 : nat, (y0 y2) -> Peano.le y1 y2)).
Definition term208 (x0 : Prop) := x0 -> ~ x0.
Definition term140 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) \/ (Peano.le x0 x1).
Definition term57 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (~ (Peano.lt y0 x0)) \/ (~ (x1 y0)).
