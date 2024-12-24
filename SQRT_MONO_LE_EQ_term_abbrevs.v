Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term35 (x0 : real) := forall y0 : real, (real_le (sqrt x0) (sqrt y0)) = (real_le x0 y0).
Definition term202 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> real_le x0 x1.
Definition term39 (x0 : real -> Prop) := ~ (all x0).
Definition term204 := (~ False) -> False.
Definition term14 := imp (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)).
Definition term11 := imp (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)).
Definition term65 (x0 : real) (x1 : real) := or ((real_le (sqrt x0) (sqrt x1)) /\ (~ (real_le x0 x1))).
Definition term34 (x0 : real) := fun y0 : real => (real_le (sqrt x0) (sqrt y0)) = (real_le x0 y0).
Definition term102 := (exists y0 : real, exists y1 : real, (real_le (sqrt y0) (sqrt y1)) /\ (~ (real_le y0 y1))) \/ (exists y0 : real, exists y1 : real, (~ (real_le (sqrt y0) (sqrt y1))) /\ (real_le y0 y1)).
Definition term72 (x0 : real) := fun y0 : real => (fun y1 : real => (real_le (sqrt x0) (sqrt y1)) /\ (~ (real_le x0 y1))) y0.
Definition term187 (x0 : Prop) := ~ (~ x0).
Definition term208 (x0 : real) (x1 : real) := (~ (~ (real_le x0 x1))) -> real_le (sqrt x0) (sqrt x1).
Definition term18 := (~ (forall y0 : real, forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> ~ (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)).
Definition term172 := and (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))).
Definition term28 (x0 : real) (x1 : real) := (real_le x0 x1) -> real_le (sqrt x0) (sqrt x1).
Definition term150 (x0 : real) := and (forall y0 : real, (~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))).
Definition term188 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term182 (x0 : real) (x1 : real) := ~ (real_le (sqrt x0) (sqrt x1)).
Definition term162 (x0 : real) := and ((fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) x0).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term107 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) \/ (real_le (sqrt x0) (sqrt x1)).
Definition term16 := (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> ~ (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)).
Definition term153 (x0 : real) := forall y0 : real, (real_lt x0 y0) \/ (real_le y0 x0).
Definition term77 (x0 : real) := fun y0 : real => (fun y1 : real => (~ (real_le (sqrt x0) (sqrt y1))) /\ (real_le x0 y1)) y0.
Definition term171 := and (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ (~ (real_le y2 y1))) y0).
Definition term149 (x0 : real) := and (forall y0 : real, (fun y1 : real => (~ (real_lt x0 y1)) \/ (~ (real_le y1 x0))) y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term41 (x0 : real) := ~ (forall y0 : real, (real_le (sqrt x0) (sqrt y0)) = (real_le x0 y0)).
Definition term183 (x0 : real) (x1 : real) := (~ (real_le (sqrt x0) (sqrt x1))) -> real_le (sqrt x0) (sqrt x1).
Definition term155 := fun y0 : real => (forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) /\ (forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0)).
Definition term88 (x0 : real) := or ((fun y0 : real => exists y1 : real, (real_le (sqrt y0) (sqrt y1)) /\ (~ (real_le y0 y1))) x0).
Definition term67 (x0 : real) (x1 : real) := (~ (real_le (sqrt x0) (sqrt x1))) /\ (real_le x0 x1).
Definition term176 := (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) /\ (forall y0 : real, forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0)).
Definition term44 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_le (sqrt x0) (sqrt y0)) = (real_le x0 y0)) x1).
Definition term120 (x0 : real) (x1 : real) := or (real_lt x0 x1).
Definition term185 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term197 (x0 : real) (x1 : real) := (real_lt x0 x1) -> ~ (real_lt x0 x1).
Definition term158 := (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ (~ (real_le y2 y1))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ (real_le y2 y1)) y0).
Definition term135 (x0 : real) := (forall y0 : real, (fun y1 : real => (~ (real_lt x0 y1)) \/ (~ (real_le y1 x0))) y0) /\ (forall y0 : real, (fun y1 : real => (real_lt x0 y1) \/ (real_le y1 x0)) y0).
Definition term200 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_lt x0 x1)).
Definition term184 (x0 : Prop) := (~ x0) -> x0.
Definition term173 := fun y0 : real => (fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ (real_le y2 y1)) y0.
Definition term168 := fun y0 : real => (fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ (~ (real_le y2 y1))) y0.
Definition term43 (x0 : real) (x1 : real) := (fun y0 : real => (real_le (sqrt x0) (sqrt y0)) = (real_le x0 y0)) x1.
Definition term78 (x0 : real) := exists y0 : real, (fun y1 : real => (~ (real_le (sqrt x0) (sqrt y1))) /\ (real_le x0 y1)) y0.
Definition term73 (x0 : real) := exists y0 : real, (fun y1 : real => (real_le (sqrt x0) (sqrt y1)) /\ (~ (real_le x0 y1))) y0.
Definition term15 := (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> False.
Definition term175 := forall y0 : real, forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0).
Definition term170 := forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0)).
Definition term129 := forall y0 : real, forall y1 : real, ((~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) /\ ((real_lt y0 y1) \/ (real_le y1 y0)).
Definition term117 := forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) \/ (real_lt (sqrt y0) (sqrt y1)).
Definition term111 := forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) \/ (real_le (sqrt y0) (sqrt y1)).
Definition term32 := forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1).
Definition term27 := forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1).
Definition term10 := forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0).
Definition term1 := forall y0 : real, forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1).
Definition term193 (x0 : real) (x1 : real) := ~ (real_lt (sqrt x0) (sqrt x1)).
Definition term61 (x0 : real) := fun y0 : real => (~ (real_le (sqrt x0) (sqrt y0))) /\ (real_le x0 y0).
Definition term127 (x0 : real) := forall y0 : real, ((~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))) /\ ((real_lt x0 y0) \/ (real_le y0 x0)).
Definition term101 := exists y0 : real, exists y1 : real, (~ (real_le (sqrt y0) (sqrt y1))) /\ (real_le y0 y1).
Definition term96 := exists y0 : real, exists y1 : real, (real_le (sqrt y0) (sqrt y1)) /\ (~ (real_le y0 y1)).
Definition term53 := exists y0 : real, exists y1 : real, ((real_le (sqrt y0) (sqrt y1)) /\ (~ (real_le y0 y1))) \/ ((~ (real_le (sqrt y0) (sqrt y1))) /\ (real_le y0 y1)).
Definition term131 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term12 := (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> False.
Definition term97 := or (exists y0 : real, (fun y1 : real => exists y2 : real, (real_le (sqrt y1) (sqrt y2)) /\ (~ (real_le y1 y2))) y0).
Definition term75 (x0 : real) := or (exists y0 : real, (fun y1 : real => (real_le (sqrt x0) (sqrt y1)) /\ (~ (real_le x0 y1))) y0).
Definition term47 (x0 : real) := exists y0 : real, ((real_le (sqrt x0) (sqrt y0)) /\ (~ (real_le x0 y0))) \/ ((~ (real_le (sqrt x0) (sqrt y0))) /\ (real_le x0 y0)).
Definition term207 (x0 : real) (x1 : real) := @eq Prop ((real_le (sqrt x0) (sqrt x1)) \/ (~ (real_le x0 x1))).
Definition term48 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_le (sqrt y1) (sqrt y2)) = (real_le y1 y2)) y0).
Definition term42 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_le (sqrt x0) (sqrt y1)) = (real_le x0 y1)) y0).
Definition term89 (x0 : real) := (fun y0 : real => exists y1 : real, (~ (real_le (sqrt y0) (sqrt y1))) /\ (real_le y0 y1)) x0.
Definition term87 (x0 : real) := (fun y0 : real => exists y1 : real, (real_le (sqrt y0) (sqrt y1)) /\ (~ (real_le y0 y1))) x0.
Definition term126 (x0 : real) := fun y0 : real => ((~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))) /\ ((real_lt x0 y0) \/ (real_le y0 x0)).
Definition term115 (x0 : real) := forall y0 : real, (~ (real_lt x0 y0)) \/ (real_lt (sqrt x0) (sqrt y0)).
Definition term109 (x0 : real) := forall y0 : real, (~ (real_le x0 y0)) \/ (real_le (sqrt x0) (sqrt y0)).
Definition term20 (x0 : real) := fun y0 : real => (~ (real_lt x0 y0)) = (real_le y0 x0).
Definition term51 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_le (sqrt y1) (sqrt y2)) = (real_le y1 y2)) y0).
Definition term167 := @eq Prop (forall y0 : real, (forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) /\ (forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0))).
Definition term166 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ (~ (real_le y2 y1))) y0) /\ ((fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ (real_le y2 y1)) y0)).
Definition term145 (x0 : real) := @eq Prop (forall y0 : real, ((~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))) /\ ((real_lt x0 y0) \/ (real_le y0 x0))).
Definition term144 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (~ (real_lt x0 y1)) \/ (~ (real_le y1 x0))) y0) /\ ((fun y1 : real => (real_lt x0 y1) \/ (real_le y1 x0)) y0)).
Definition term85 := fun y0 : real => exists y1 : real, (real_le (sqrt y0) (sqrt y1)) /\ (~ (real_le y0 y1)).
Definition term206 (x0 : real) (x1 : real) := @eq Prop ((~ (real_le x0 x1)) \/ (real_le (sqrt x0) (sqrt x1))).
Definition term139 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) \/ (~ (real_le x0 x1)).
Definition term128 := fun y0 : real => forall y1 : real, ((~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) /\ ((real_lt y0 y1) \/ (real_le y1 y0)).
Definition term116 := fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (real_lt (sqrt y0) (sqrt y1)).
Definition term110 := fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (real_le (sqrt y0) (sqrt y1)).
Definition term31 := fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1).
Definition term26 := fun y0 : real => forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1).
Definition term8 := (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> False.
Definition term198 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_lt x0 x1).
Definition term90 (x0 : real) := ((fun y0 : real => exists y1 : real, (real_le (sqrt y0) (sqrt y1)) /\ (~ (real_le y0 y1))) x0) \/ ((fun y0 : real => exists y1 : real, (~ (real_le (sqrt y0) (sqrt y1))) /\ (real_le y0 y1)) x0).
Definition term125 (x0 : real) (x1 : real) := ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))) /\ ((real_lt x1 x0) \/ (real_le x0 x1)).
Definition term46 (x0 : real) := fun y0 : real => ((real_le (sqrt x0) (sqrt y0)) /\ (~ (real_le x0 y0))) \/ ((~ (real_le (sqrt x0) (sqrt y0))) /\ (real_le x0 y0)).
Definition term21 (x0 : real) := forall y0 : real, (~ (real_lt x0 y0)) = (real_le y0 x0).
Definition term7 := (((~ (forall y0 : real, forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> False) -> ((~ (forall y0 : real, forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> False.
Definition term56 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term80 (x0 : real) := (exists y0 : real, (real_le (sqrt x0) (sqrt y0)) /\ (~ (real_le x0 y0))) \/ (exists y0 : real, (~ (real_le (sqrt x0) (sqrt y0))) /\ (real_le x0 y0)).
Definition term9 := ~ (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)).
Definition term3 := ~ (forall y0 : real, forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1)).
Definition term5 := ((~ (forall y0 : real, forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> False.
Definition term19 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term74 (x0 : real) := exists y0 : real, (real_le (sqrt x0) (sqrt y0)) /\ (~ (real_le x0 y0)).
Definition term99 := fun y0 : real => (fun y1 : real => exists y2 : real, (~ (real_le (sqrt y1) (sqrt y2))) /\ (real_le y1 y2)) y0.
Definition term94 := fun y0 : real => (fun y1 : real => exists y2 : real, (real_le (sqrt y1) (sqrt y2)) /\ (~ (real_le y1 y2))) y0.
Definition term57 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term154 (x0 : real) := (forall y0 : real, (~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))) /\ (forall y0 : real, (real_lt x0 y0) \/ (real_le y0 x0)).
Definition term50 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1)) x0).
Definition term52 := fun y0 : real => exists y1 : real, ((real_le (sqrt y0) (sqrt y1)) /\ (~ (real_le y0 y1))) \/ ((~ (real_le (sqrt y0) (sqrt y1))) /\ (real_le y0 y1)).
Definition term6 := (((~ (forall y0 : real, forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> False.
Definition term178 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_lt x0 y0)) \/ (real_lt (sqrt x0) (sqrt y0))) x1.
Definition term191 (x0 : real) (x1 : real) := (real_le x1 x0) -> ~ (real_lt x0 x1).
Definition term148 (x0 : real) := forall y0 : real, (~ (real_lt x0 y0)) \/ (~ (real_le y0 x0)).
Definition term123 (x0 : real) (x1 : real) := and ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))).
Definition term146 (x0 : real) := fun y0 : real => (fun y1 : real => (~ (real_lt x0 y1)) \/ (~ (real_le y1 x0))) y0.
Definition term180 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_le x0 y0)) \/ (real_le (sqrt x0) (sqrt y0))) x1.
Definition term93 := @eq Prop (exists y0 : real, (exists y1 : real, (real_le (sqrt y0) (sqrt y1)) /\ (~ (real_le y0 y1))) \/ (exists y1 : real, (~ (real_le (sqrt y0) (sqrt y1))) /\ (real_le y0 y1))).
Definition term92 := @eq Prop (exists y0 : real, ((fun y1 : real => exists y2 : real, (real_le (sqrt y1) (sqrt y2)) /\ (~ (real_le y1 y2))) y0) \/ ((fun y1 : real => exists y2 : real, (~ (real_le (sqrt y1) (sqrt y2))) /\ (real_le y1 y2)) y0)).
Definition term71 (x0 : real) := @eq Prop (exists y0 : real, ((real_le (sqrt x0) (sqrt y0)) /\ (~ (real_le x0 y0))) \/ ((~ (real_le (sqrt x0) (sqrt y0))) /\ (real_le x0 y0))).
Definition term70 (x0 : real) := @eq Prop (exists y0 : real, ((fun y1 : real => (real_le (sqrt x0) (sqrt y1)) /\ (~ (real_le x0 y1))) y0) \/ ((fun y1 : real => (~ (real_le (sqrt x0) (sqrt y1))) /\ (real_le x0 y1)) y0)).
Definition term33 (x0 : real) (x1 : real) := real_le (sqrt x0) (sqrt x1).
Definition term124 (x0 : real) (x1 : real) := ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))) /\ ((~ (~ (real_lt x1 x0))) \/ (real_le x0 x1)).
Definition term160 := fun y0 : real => forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0).
Definition term36 := fun y0 : real => forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1).
Definition term22 := fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0).
Definition term29 (x0 : real) := fun y0 : real => (real_le x0 y0) -> real_le (sqrt x0) (sqrt y0).
Definition term40 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term132 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term186 (x0 : real) (x1 : real) := (~ (~ (real_le x1 x0))) -> ~ (real_lt x0 x1).
Definition term179 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (real_le (sqrt y0) (sqrt y1))) x0.
Definition term177 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (real_lt (sqrt y0) (sqrt y1))) x0.
Definition term163 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0)) x0.
Definition term161 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) x0.
Definition term49 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1)) x0.
Definition term114 (x0 : real) := fun y0 : real => (~ (real_lt x0 y0)) \/ (real_lt (sqrt x0) (sqrt y0)).
Definition term121 (x0 : real) (x1 : real) := (~ (~ (real_lt x1 x0))) \/ (real_le x0 x1).
Definition term60 (x0 : real) := fun y0 : real => (real_le (sqrt x0) (sqrt y0)) /\ (~ (real_le x0 y0)).
Definition term37 (x0 : real) (x1 : real) := ~ ((real_le (sqrt x0) (sqrt x1)) = (real_le x0 x1)).
Definition term2 := (~ (forall y0 : real, forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1))) -> False.
Definition term152 (x0 : real) := forall y0 : real, (fun y1 : real => (real_lt x0 y1) \/ (real_le y1 x0)) y0.
Definition term147 (x0 : real) := forall y0 : real, (fun y1 : real => (~ (real_lt x0 y1)) \/ (~ (real_le y1 x0))) y0.
Definition term38 (x0 : real) (x1 : real) := ((real_le (sqrt x0) (sqrt x1)) /\ (~ (real_le x0 x1))) \/ ((~ (real_le (sqrt x0) (sqrt x1))) /\ (real_le x0 x1)).
Definition term112 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) \/ (real_lt (sqrt x0) (sqrt x1)).
Definition term137 (x0 : real) := fun y0 : real => (real_lt x0 y0) \/ (real_le y0 x0).
Definition term4 := (~ (forall y0 : real, forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)) -> False.
Definition term165 := fun y0 : real => ((fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ (~ (real_le y2 y1))) y0) /\ ((fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ (real_le y2 y1)) y0).
Definition term199 (x0 : real) (x1 : real) := @eq Prop ((real_lt x1 x0) \/ (real_le x0 x1)).
Definition term63 (x0 : real) (x1 : real) := (real_le (sqrt x0) (sqrt x1)) /\ (~ (real_le x0 x1)).
Definition term142 (x0 : real) (x1 : real) := ((fun y0 : real => (~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))) x1) /\ ((fun y0 : real => (real_lt x0 y0) \/ (real_le y0 x0)) x1).
Definition term138 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))) x1.
Definition term69 (x0 : real) := fun y0 : real => ((fun y1 : real => (real_le (sqrt x0) (sqrt y1)) /\ (~ (real_le x0 y1))) y0) \/ ((fun y1 : real => (~ (real_le (sqrt x0) (sqrt y1))) /\ (real_le x0 y1)) y0).
Definition term83 := exists y0 : real, ((fun y1 : real => exists y2 : real, (real_le (sqrt y1) (sqrt y2)) /\ (~ (real_le y1 y2))) y0) \/ ((fun y1 : real => exists y2 : real, (~ (real_le (sqrt y1) (sqrt y2))) /\ (real_le y1 y2)) y0).
Definition term58 (x0 : real) := exists y0 : real, ((fun y1 : real => (real_le (sqrt x0) (sqrt y1)) /\ (~ (real_le x0 y1))) y0) \/ ((fun y1 : real => (~ (real_le (sqrt x0) (sqrt y1))) /\ (real_le x0 y1)) y0).
Definition term136 (x0 : real) := fun y0 : real => (~ (real_lt x0 y0)) \/ (~ (real_le y0 x0)).
Definition term196 (x0 : real) (x1 : real) := (~ (real_lt (sqrt x0) (sqrt x1))) -> ~ (real_lt x0 x1).
Definition term118 (x0 : real) (x1 : real) := ~ (~ (real_lt x0 x1)).
Definition term86 := fun y0 : real => exists y1 : real, (~ (real_le (sqrt y0) (sqrt y1))) /\ (real_le y0 y1).
Definition term30 (x0 : real) := forall y0 : real, (real_le x0 y0) -> real_le (sqrt x0) (sqrt y0).
Definition term25 (x0 : real) := forall y0 : real, (real_lt x0 y0) -> real_lt (sqrt x0) (sqrt y0).
Definition term190 (x0 : real) (x1 : real) := imp (real_le x0 x1).
Definition term181 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term64 (x0 : real) (x1 : real) := or ((fun y0 : real => (real_le (sqrt x0) (sqrt y0)) /\ (~ (real_le x0 y0))) x1).
Definition term156 := forall y0 : real, (forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) /\ (forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0)).
Definition term113 (x0 : real) (x1 : real) := real_lt (sqrt x0) (sqrt x1).
Definition term194 (x0 : real) (x1 : real) := (real_lt (sqrt x0) (sqrt x1)) -> ~ (real_lt (sqrt x0) (sqrt x1)).
Definition term174 := forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ (real_le y2 y1)) y0.
Definition term169 := forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ (~ (real_le y2 y1))) y0.
Definition term68 (x0 : real) (x1 : real) := ((fun y0 : real => (real_le (sqrt x0) (sqrt y0)) /\ (~ (real_le x0 y0))) x1) \/ ((fun y0 : real => (~ (real_le (sqrt x0) (sqrt y0))) /\ (real_le x0 y0)) x1).
Definition term122 (x0 : real) (x1 : real) := (real_lt x1 x0) \/ (real_le x0 x1).
Definition term164 (x0 : real) := ((fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0))) x0) /\ ((fun y0 : real => forall y1 : real, (real_lt y0 y1) \/ (real_le y1 y0)) x0).
Definition term13 := (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> ~ (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) = (real_le y1 y0)).
Definition term143 (x0 : real) := fun y0 : real => ((fun y1 : real => (~ (real_lt x0 y1)) \/ (~ (real_le y1 x0))) y0) /\ ((fun y1 : real => (real_lt x0 y1) \/ (real_le y1 x0)) y0).
Definition term151 (x0 : real) := fun y0 : real => (fun y1 : real => (real_lt x0 y1) \/ (real_le y1 x0)) y0.
Definition term45 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_le (sqrt x0) (sqrt y1)) = (real_le x0 y1)) y0).
Definition term62 (x0 : real) (x1 : real) := (fun y0 : real => (real_le (sqrt x0) (sqrt y0)) /\ (~ (real_le x0 y0))) x1.
Definition term133 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term119 (x0 : real) (x1 : real) := or (~ (~ (real_lt x0 x1))).
Definition term108 (x0 : real) := fun y0 : real => (~ (real_le x0 y0)) \/ (real_le (sqrt x0) (sqrt y0)).
Definition term66 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_le (sqrt x0) (sqrt y0))) /\ (real_le x0 y0)) x1.
Definition term130 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term192 (x0 : real) (x1 : real) := (real_le (sqrt x1) (sqrt x0)) -> ~ (real_lt (sqrt x0) (sqrt x1)).
Definition term140 (x0 : real) (x1 : real) := and ((fun y0 : real => (~ (real_lt x0 y0)) \/ (~ (real_le y0 x0))) x1).
Definition term82 := exists y0 : real, (exists y1 : real, (real_le (sqrt y0) (sqrt y1)) /\ (~ (real_le y0 y1))) \/ (exists y1 : real, (~ (real_le (sqrt y0) (sqrt y1))) /\ (real_le y0 y1)).
Definition term23 (x0 : real) (x1 : real) := (real_lt x0 x1) -> real_lt (sqrt x0) (sqrt x1).
Definition term209 (x0 : real) (x1 : real) := (real_le (sqrt x0) (sqrt x1)) -> False.
Definition term91 := fun y0 : real => ((fun y1 : real => exists y2 : real, (real_le (sqrt y1) (sqrt y2)) /\ (~ (real_le y1 y2))) y0) \/ ((fun y1 : real => exists y2 : real, (~ (real_le (sqrt y1) (sqrt y2))) /\ (real_le y1 y2)) y0).
Definition term203 (x0 : real) (x1 : real) := (real_le x0 x1) -> False.
Definition term76 (x0 : real) := or (exists y0 : real, (real_le (sqrt x0) (sqrt y0)) /\ (~ (real_le x0 y0))).
Definition term98 := or (exists y0 : real, exists y1 : real, (real_le (sqrt y0) (sqrt y1)) /\ (~ (real_le y0 y1))).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term81 := fun y0 : real => (exists y1 : real, (real_le (sqrt y0) (sqrt y1)) /\ (~ (real_le y0 y1))) \/ (exists y1 : real, (~ (real_le (sqrt y0) (sqrt y1))) /\ (real_le y0 y1)).
Definition term24 (x0 : real) := fun y0 : real => (real_lt x0 y0) -> real_lt (sqrt x0) (sqrt y0).
Definition term157 := forall y0 : real, ((fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ (~ (real_le y2 y1))) y0) /\ ((fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ (real_le y2 y1)) y0).
Definition term134 (x0 : real) := forall y0 : real, ((fun y1 : real => (~ (real_lt x0 y1)) \/ (~ (real_le y1 x0))) y0) /\ ((fun y1 : real => (real_lt x0 y1) \/ (real_le y1 x0)) y0).
Definition term201 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) -> real_le x0 x1.
Definition term84 := (exists y0 : real, (fun y1 : real => exists y2 : real, (real_le (sqrt y1) (sqrt y2)) /\ (~ (real_le y1 y2))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (~ (real_le (sqrt y1) (sqrt y2))) /\ (real_le y1 y2)) y0).
Definition term59 (x0 : real) := (exists y0 : real, (fun y1 : real => (real_le (sqrt x0) (sqrt y1)) /\ (~ (real_le x0 y1))) y0) \/ (exists y0 : real, (fun y1 : real => (~ (real_le (sqrt x0) (sqrt y1))) /\ (real_le x0 y1)) y0).
Definition term141 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt x0 y0) \/ (real_le y0 x0)) x1.
Definition term17 := imp (~ (forall y0 : real, forall y1 : real, (real_le (sqrt y0) (sqrt y1)) = (real_le y0 y1))).
Definition term195 (x0 : Prop) := x0 -> ~ x0.
Definition term159 := fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (~ (real_le y1 y0)).
Definition term79 (x0 : real) := exists y0 : real, (~ (real_le (sqrt x0) (sqrt y0))) /\ (real_le x0 y0).
Definition term205 (x0 : real) (x1 : real) := (real_le (sqrt x0) (sqrt x1)) \/ (~ (real_le x0 x1)).
Definition term189 (x0 : real) (x1 : real) := imp (~ (~ (real_le x0 x1))).
Definition term100 := exists y0 : real, (fun y1 : real => exists y2 : real, (~ (real_le (sqrt y1) (sqrt y2))) /\ (real_le y1 y2)) y0.
Definition term95 := exists y0 : real, (fun y1 : real => exists y2 : real, (real_le (sqrt y1) (sqrt y2)) /\ (~ (real_le y1 y2))) y0.
Definition term106 (x0 : real) := @eq Prop ((exists y0 : real, (real_le (sqrt x0) (sqrt y0)) /\ (~ (real_le x0 y0))) \/ (exists y0 : real, (~ (real_le (sqrt x0) (sqrt y0))) /\ (real_le x0 y0))).
Definition term105 (x0 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => (real_le (sqrt x0) (sqrt y1)) /\ (~ (real_le x0 y1))) y0) \/ (exists y0 : real, (fun y1 : real => (~ (real_le (sqrt x0) (sqrt y1))) /\ (real_le x0 y1)) y0)).
Definition term104 := @eq Prop ((exists y0 : real, exists y1 : real, (real_le (sqrt y0) (sqrt y1)) /\ (~ (real_le y0 y1))) \/ (exists y0 : real, exists y1 : real, (~ (real_le (sqrt y0) (sqrt y1))) /\ (real_le y0 y1))).
Definition term103 := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, (real_le (sqrt y1) (sqrt y2)) /\ (~ (real_le y1 y2))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (~ (real_le (sqrt y1) (sqrt y2))) /\ (real_le y1 y2)) y0)).
