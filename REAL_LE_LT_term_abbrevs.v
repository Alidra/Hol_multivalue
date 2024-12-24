Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term41 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term53 (x0 : real) (x1 : real) := (real_le x1 x0) /\ (~ (x0 = x1)).
Definition term205 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> real_le x0 x1.
Definition term63 (x0 : real -> Prop) := ~ (all x0).
Definition term224 := (~ False) -> False.
Definition term198 (x0 : real) := fun y0 : real => ~ (real_le y0 x0).
Definition term203 (x0 : real) (x1 : real) := @eq Prop (~ (real_le x0 x1)).
Definition term34 := imp (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term123 := (exists y0 : real, exists y1 : real, (real_le y0 y1) /\ ((real_le y1 y0) /\ (~ (y0 = y1)))) \/ (exists y0 : real, exists y1 : real, (~ (real_le y0 y1)) /\ ((~ (real_le y1 y0)) \/ (y0 = y1))).
Definition term218 (x0 : Prop) := ~ (~ x0).
Definition term183 := and (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))).
Definition term17 (x0 : real) := fun y0 : real => (real_le x0 y0) = ((~ (real_le y0 x0)) \/ (x0 = y0)).
Definition term161 (x0 : real) := and (forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))).
Definition term48 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term173 (x0 : real) := and ((fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) x0).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term128 (x0 : real) (x1 : real) := ~ ((real_le x1 x0) /\ (real_le x0 x1)).
Definition term45 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_le y0 x0).
Definition term9 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt y0 x0) = (~ (real_le x0 y0))) x1.
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term182 := and (forall y0 : real, (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0).
Definition term160 (x0 : real) := and (forall y0 : real, (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0).
Definition term24 (x0 : Prop) := (~ x0) -> False.
Definition term219 (x0 : real) (x1 : real) := imp (~ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1)))).
Definition term65 (x0 : real) := ~ (forall y0 : real, (real_le x0 y0) = ((~ (real_le y0 x0)) \/ (x0 = y0))).
Definition term137 (x0 : real) := fun y0 : real => (((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)).
Definition term55 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) /\ ((~ (real_le x1 x0)) \/ (x0 = x1)).
Definition term166 := fun y0 : real => (forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term62 (x0 : real) (x1 : real) := ~ ((real_le x0 x1) = ((~ (real_le x1 x0)) \/ (x0 = x1))).
Definition term223 (x0 : real) (x1 : real) := (x0 = x1) -> False.
Definition term109 (x0 : real) := or ((fun y0 : real => exists y1 : real, (real_le y0 y1) /\ ((real_le y1 y0) /\ (~ (y0 = y1)))) x0).
Definition term43 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_le x0 x1).
Definition term60 (x0 : real) (x1 : real) := ((real_le x0 x1) /\ (~ ((~ (real_le x1 x0)) \/ (x0 = x1)))) \/ ((~ (real_le x0 x1)) /\ ((~ (real_le x1 x0)) \/ (x0 = x1))).
Definition term221 (x0 : real) (x1 : real) := ((real_le x0 x1) /\ (real_le x1 x0)) -> x0 = x1.
Definition term187 := (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y0 : real, forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term68 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_le x0 y0) = ((~ (real_le y0 x0)) \/ (x0 = y0))) x1).
Definition term11 (x0 : real) (x1 : real) := or (real_lt x0 x1).
Definition term212 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term58 (x0 : real) (x1 : real) := or ((real_le x0 x1) /\ (~ ((~ (real_le x1 x0)) \/ (x0 = x1)))).
Definition term169 := (forall y0 : real, (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0).
Definition term146 (x0 : real) := (forall y0 : real, (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ (forall y0 : real, (fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0).
Definition term85 (x0 : real) := fun y0 : real => (~ (real_le x0 y0)) /\ ((~ (real_le y0 x0)) \/ (x0 = y0)).
Definition term133 (x0 : real) (x1 : real) := ((~ (real_le x0 x1)) \/ (~ (real_le x1 x0))) \/ (x0 = x1).
Definition term230 (x0 : real) := (~ (x0 = x0)) -> x0 = x0.
Definition term130 (x0 : real) (x1 : real) := or (~ ((real_le x1 x0) /\ (real_le x0 x1))).
Definition term61 (x0 : real) (x1 : real) := ((real_le x0 x1) /\ ((real_le x1 x0) /\ (~ (x0 = x1)))) \/ ((~ (real_le x0 x1)) /\ ((~ (real_le x1 x0)) \/ (x0 = x1))).
Definition term206 (x0 : Prop) := (~ x0) -> x0.
Definition term132 (x0 : real) (x1 : real) := (~ ((real_le x0 x1) /\ (real_le x1 x0))) \/ (x0 = x1).
Definition term28 := ((~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False.
Definition term14 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ (x0 = x1).
Definition term184 := fun y0 : real => (fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0.
Definition term179 := fun y0 : real => (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0.
Definition term215 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term232 (x0 : real) (x1 : real) := (~ (~ (x1 = x0))) -> real_le x0 x1.
Definition term135 (x0 : real) (x1 : real) := (((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1))) /\ ((~ ((real_le x0 x1) /\ (real_le x1 x0))) \/ (x0 = x1)).
Definition term99 (x0 : real) := exists y0 : real, (fun y1 : real => (~ (real_le x0 y1)) /\ ((~ (real_le y1 x0)) \/ (x0 = y1))) y0.
Definition term94 (x0 : real) := exists y0 : real, (fun y1 : real => (real_le x0 y1) /\ ((real_le y1 x0) /\ (~ (x0 = y1)))) y0.
Definition term192 := forall y0 : real, forall y1 : real, ((real_le y0 y1) \/ (~ (y0 = y1))) /\ ((real_le y1 y0) \/ (~ (y0 = y1))).
Definition term186 := forall y0 : real, forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1).
Definition term181 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1)).
Definition term140 := forall y0 : real, forall y1 : real, (((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term47 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term33 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term23 := forall y0 : real, forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1)).
Definition term22 := forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1)).
Definition term138 (x0 : real) := forall y0 : real, (((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)).
Definition term122 := exists y0 : real, exists y1 : real, (~ (real_le y0 y1)) /\ ((~ (real_le y1 y0)) \/ (y0 = y1)).
Definition term117 := exists y0 : real, exists y1 : real, (real_le y0 y1) /\ ((real_le y1 y0) /\ (~ (y0 = y1))).
Definition term77 := exists y0 : real, exists y1 : real, ((real_le y0 y1) /\ ((real_le y1 y0) /\ (~ (y0 = y1)))) \/ ((~ (real_le y0 y1)) /\ ((~ (real_le y1 y0)) \/ (y0 = y1))).
Definition term142 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term35 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False.
Definition term222 (x0 : real) (x1 : real) := (~ (x0 = x1)) -> x0 = x1.
Definition term118 := or (exists y0 : real, (fun y1 : real => exists y2 : real, (real_le y1 y2) /\ ((real_le y2 y1) /\ (~ (y1 = y2)))) y0).
Definition term96 (x0 : real) := or (exists y0 : real, (fun y1 : real => (real_le x0 y1) /\ ((real_le y1 x0) /\ (~ (x0 = y1)))) y0).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term38 := (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)).
Definition term86 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) /\ ((real_le y0 x0) /\ (~ (x0 = y0)))) x1.
Definition term213 (x0 : real) (x1 : real) := (~ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x0)))) -> x0 = x1.
Definition term211 (x0 : real) (x1 : real) := @eq Prop ((x1 = x0) \/ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1)))).
Definition term201 (x0 : real) := ~ (real_le x0 x0).
Definition term84 (x0 : real) := fun y0 : real => (real_le x0 y0) /\ ((real_le y0 x0) /\ (~ (x0 = y0))).
Definition term204 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (~ (x0 = x1)).
Definition term72 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_le y1 y2) = ((~ (real_le y2 y1)) \/ (y1 = y2))) y0).
Definition term66 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_le x0 y1) = ((~ (real_le y1 x0)) \/ (x0 = y1))) y0).
Definition term110 (x0 : real) := (fun y0 : real => exists y1 : real, (~ (real_le y0 y1)) /\ ((~ (real_le y1 y0)) \/ (y0 = y1))) x0.
Definition term108 (x0 : real) := (fun y0 : real => exists y1 : real, (real_le y0 y1) /\ ((real_le y1 y0) /\ (~ (y0 = y1)))) x0.
Definition term75 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_le y1 y2) = ((~ (real_le y2 y1)) \/ (y1 = y2))) y0).
Definition term178 := @eq Prop (forall y0 : real, (forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1))).
Definition term177 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0)).
Definition term156 (x0 : real) := @eq Prop (forall y0 : real, (((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0))).
Definition term155 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0)).
Definition term136 (x0 : real) (x1 : real) := (((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1))) /\ (((~ (real_le x0 x1)) \/ (~ (real_le x1 x0))) \/ (x0 = x1)).
Definition term129 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ (~ (real_le x0 x1)).
Definition term70 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ ((real_le y0 x0) /\ (~ (x0 = y0)))) \/ ((~ (real_le x0 y0)) /\ ((~ (real_le y0 x0)) \/ (x0 = y0))).
Definition term191 := fun y0 : real => forall y1 : real, ((real_le y0 y1) \/ (~ (y0 = y1))) /\ ((real_le y1 y0) \/ (~ (y0 = y1))).
Definition term139 := fun y0 : real => forall y1 : real, (((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term21 := fun y0 : real => forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1)).
Definition term20 := fun y0 : real => forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1)).
Definition term238 (x0 : real) := (~ (real_le x0 x0)) -> real_le x0 x0.
Definition term31 := (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False.
Definition term111 (x0 : real) := ((fun y0 : real => exists y1 : real, (real_le y0 y1) /\ ((real_le y1 y0) /\ (~ (y0 = y1)))) x0) \/ ((fun y0 : real => exists y1 : real, (~ (real_le y0 y1)) /\ ((~ (real_le y1 y0)) \/ (y0 = y1))) x0).
Definition term39 (x0 : real) (x1 : real) := (real_le x1 x0) /\ (real_le x0 x1).
Definition term49 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term80 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term101 (x0 : real) := (exists y0 : real, (real_le x0 y0) /\ ((real_le y0 x0) /\ (~ (x0 = y0)))) \/ (exists y0 : real, (~ (real_le x0 y0)) /\ ((~ (real_le y0 x0)) \/ (x0 = y0))).
Definition term32 := ~ (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)).
Definition term26 := ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1))).
Definition term148 (x0 : real) := fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term225 (x0 : real) (x1 : real) := (real_le x0 x1) -> ~ (real_le x0 x1).
Definition term120 := fun y0 : real => (fun y1 : real => exists y2 : real, (~ (real_le y1 y2)) /\ ((~ (real_le y2 y1)) \/ (y1 = y2))) y0.
Definition term115 := fun y0 : real => (fun y1 : real => exists y2 : real, (real_le y1 y2) /\ ((real_le y2 y1) /\ (~ (y1 = y2)))) y0.
Definition term81 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term214 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term165 (x0 : real) := (forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (forall y0 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)).
Definition term190 (x0 : real) := forall y0 : real, ((real_le x0 y0) \/ (~ (x0 = y0))) /\ ((real_le y0 x0) \/ (~ (x0 = y0))).
Definition term208 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ ((x1 = x0) \/ (~ (real_le x0 x1))).
Definition term74 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1))) x0).
Definition term107 := fun y0 : real => exists y1 : real, (~ (real_le y0 y1)) /\ ((~ (real_le y1 y0)) \/ (y0 = y1)).
Definition term106 := fun y0 : real => exists y1 : real, (real_le y0 y1) /\ ((real_le y1 y0) /\ (~ (y0 = y1))).
Definition term76 := fun y0 : real => exists y1 : real, ((real_le y0 y1) /\ ((real_le y1 y0) /\ (~ (y0 = y1)))) \/ ((~ (real_le y0 y1)) /\ ((~ (real_le y1 y0)) \/ (y0 = y1))).
Definition term147 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0)).
Definition term15 (x0 : real) (x1 : real) := @eq Prop (real_le x0 x1).
Definition term157 (x0 : real) := fun y0 : real => (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0.
Definition term134 (x0 : real) (x1 : real) := and (((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1))).
Definition term29 := (((~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False.
Definition term152 (x0 : real) (x1 : real) := (fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)) x1.
Definition term114 := @eq Prop (exists y0 : real, (exists y1 : real, (real_le y0 y1) /\ ((real_le y1 y0) /\ (~ (y0 = y1)))) \/ (exists y1 : real, (~ (real_le y0 y1)) /\ ((~ (real_le y1 y0)) \/ (y0 = y1)))).
Definition term113 := @eq Prop (exists y0 : real, ((fun y1 : real => exists y2 : real, (real_le y1 y2) /\ ((real_le y2 y1) /\ (~ (y1 = y2)))) y0) \/ ((fun y1 : real => exists y2 : real, (~ (real_le y1 y2)) /\ ((~ (real_le y2 y1)) \/ (y1 = y2))) y0)).
Definition term92 (x0 : real) := @eq Prop (exists y0 : real, ((real_le x0 y0) /\ ((real_le y0 x0) /\ (~ (x0 = y0)))) \/ ((~ (real_le x0 y0)) /\ ((~ (real_le y0 x0)) \/ (x0 = y0)))).
Definition term91 (x0 : real) := @eq Prop (exists y0 : real, ((fun y1 : real => (real_le x0 y1) /\ ((real_le y1 x0) /\ (~ (x0 = y1)))) y0) \/ ((fun y1 : real => (~ (real_le x0 y1)) /\ ((~ (real_le y1 x0)) \/ (x0 = y1))) y0)).
Definition term171 := fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1).
Definition term46 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term42 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term64 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term143 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term195 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_le y0 y1) \/ (~ (y0 = y1))) /\ ((real_le y1 y0) \/ (~ (y0 = y1)))) x0.
Definition term193 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) x0.
Definition term174 (x0 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)) x0.
Definition term172 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) x0.
Definition term73 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1))) x0.
Definition term7 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) x0.
Definition term59 (x0 : real) (x1 : real) := or ((real_le x0 x1) /\ ((real_le x1 x0) /\ (~ (x0 = x1)))).
Definition term131 (x0 : real) (x1 : real) := or ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1))).
Definition term25 := (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1)))) -> False.
Definition term163 (x0 : real) := forall y0 : real, (fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0.
Definition term158 (x0 : real) := forall y0 : real, (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0.
Definition term44 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0).
Definition term88 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_le x0 y0)) /\ ((~ (real_le y0 x0)) \/ (x0 = y0))) x1.
Definition term176 := fun y0 : real => ((fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0).
Definition term227 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_le x0 x1)).
Definition term209 (x0 : real) (x1 : real) := (x1 = x0) \/ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1))).
Definition term40 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term197 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) \/ ((~ (real_le x1 x0)) \/ (x0 = x1)).
Definition term30 := (((~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False) -> ((~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False.
Definition term12 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term153 (x0 : real) (x1 : real) := ((fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) x1) /\ ((fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)) x1).
Definition term50 (x0 : real) (x1 : real) := and (~ (~ (real_le x0 x1))).
Definition term207 (x0 : real) (x1 : real) := (x1 = x0) \/ (~ (real_le x0 x1)).
Definition term16 (x0 : real) := fun y0 : real => (real_le x0 y0) = ((real_lt x0 y0) \/ (x0 = y0)).
Definition term90 (x0 : real) := fun y0 : real => ((fun y1 : real => (real_le x0 y1) /\ ((real_le y1 x0) /\ (~ (x0 = y1)))) y0) \/ ((fun y1 : real => (~ (real_le x0 y1)) /\ ((~ (real_le y1 x0)) \/ (x0 = y1))) y0).
Definition term8 (x0 : real) := forall y0 : real, (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term189 (x0 : real) := fun y0 : real => ((real_le x0 y0) \/ (~ (x0 = y0))) /\ ((real_le y0 x0) \/ (~ (x0 = y0))).
Definition term104 := exists y0 : real, ((fun y1 : real => exists y2 : real, (real_le y1 y2) /\ ((real_le y2 y1) /\ (~ (y1 = y2)))) y0) \/ ((fun y1 : real => exists y2 : real, (~ (real_le y1 y2)) /\ ((~ (real_le y2 y1)) \/ (y1 = y2))) y0).
Definition term82 (x0 : real) := exists y0 : real, ((fun y1 : real => (real_le x0 y1) /\ ((real_le y1 x0) /\ (~ (x0 = y1)))) y0) \/ ((fun y1 : real => (~ (real_le x0 y1)) /\ ((~ (real_le y1 x0)) \/ (x0 = y1))) y0).
Definition term220 (x0 : real) (x1 : real) := imp ((real_le x1 x0) /\ (real_le x0 x1)).
Definition term56 (x0 : real) (x1 : real) := (real_le x0 x1) /\ (~ ((~ (real_le x1 x0)) \/ (x0 = x1))).
Definition term200 (x0 : real) := (fun y0 : real => ~ (real_le y0 x0)) x0.
Definition term196 (x0 : real) (x1 : real) := (fun y0 : real => ((real_le x0 y0) \/ (~ (x0 = y0))) /\ ((real_le y0 x0) \/ (~ (x0 = y0)))) x1.
Definition term10 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term87 (x0 : real) (x1 : real) := or ((fun y0 : real => (real_le x0 y0) /\ ((real_le y0 x0) /\ (~ (x0 = y0)))) x1).
Definition term167 := forall y0 : real, (forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term54 (x0 : real) (x1 : real) := ~ ((~ (real_le x1 x0)) \/ (x0 = x1)).
Definition term95 (x0 : real) := exists y0 : real, (real_le x0 y0) /\ ((real_le y0 x0) /\ (~ (x0 = y0))).
Definition term216 (x0 : real) (x1 : real) := ~ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1))).
Definition term202 (x0 : real) (x1 : real) := @eq Prop ((fun y0 : real => ~ (real_le y0 x0)) x1).
Definition term13 (x0 : real) (x1 : real) := (real_lt x0 x1) \/ (x0 = x1).
Definition term98 (x0 : real) := fun y0 : real => (fun y1 : real => (~ (real_le x0 y1)) /\ ((~ (real_le y1 x0)) \/ (x0 = y1))) y0.
Definition term93 (x0 : real) := fun y0 : real => (fun y1 : real => (real_le x0 y1) /\ ((real_le y1 x0) /\ (~ (x0 = y1)))) y0.
Definition term67 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) = ((~ (real_le y0 x0)) \/ (x0 = y0))) x1.
Definition term185 := forall y0 : real, (fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0.
Definition term180 := forall y0 : real, (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0.
Definition term89 (x0 : real) (x1 : real) := ((fun y0 : real => (real_le x0 y0) /\ ((real_le y0 x0) /\ (~ (x0 = y0)))) x1) \/ ((fun y0 : real => (~ (real_le x0 y0)) /\ ((~ (real_le y0 x0)) \/ (x0 = y0))) x1).
Definition term175 (x0 : real) := ((fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) x0) /\ ((fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)) x0).
Definition term36 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)).
Definition term51 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term231 (x0 : real) := ~ (x0 = x0).
Definition term154 (x0 : real) := fun y0 : real => ((fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0).
Definition term162 (x0 : real) := fun y0 : real => (fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term69 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_le x0 y1) = ((~ (real_le y1 x0)) \/ (x0 = y1))) y0).
Definition term149 (x0 : real) (x1 : real) := (fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) x1.
Definition term71 (x0 : real) := exists y0 : real, ((real_le x0 y0) /\ ((real_le y0 x0) /\ (~ (x0 = y0)))) \/ ((~ (real_le x0 y0)) /\ ((~ (real_le y0 x0)) \/ (x0 = y0))).
Definition term188 (x0 : real) (x1 : real) := ((real_le x0 x1) \/ (~ (x0 = x1))) /\ ((real_le x1 x0) \/ (~ (x0 = x1))).
Definition term144 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term210 (x0 : real) (x1 : real) := @eq Prop ((~ (real_le x0 x1)) \/ ((~ (real_le x1 x0)) \/ (x0 = x1))).
Definition term237 (x0 : real) := (x0 = x0) -> real_le x0 x0.
Definition term141 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term100 (x0 : real) := exists y0 : real, (~ (real_le x0 y0)) /\ ((~ (real_le y0 x0)) \/ (x0 = y0)).
Definition term236 (x0 : real) (x1 : real) := (x1 = x0) -> real_le x0 x1.
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term19 (x0 : real) := forall y0 : real, (real_le x0 y0) = ((~ (real_le y0 x0)) \/ (x0 = y0)).
Definition term18 (x0 : real) := forall y0 : real, (real_le x0 y0) = ((real_lt x0 y0) \/ (x0 = y0)).
Definition term199 (x0 : real) (x1 : real) := (fun y0 : real => ~ (real_le y0 x0)) x1.
Definition term233 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term151 (x0 : real) (x1 : real) := and ((fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) x1).
Definition term103 := exists y0 : real, (exists y1 : real, (real_le y0 y1) /\ ((real_le y1 y0) /\ (~ (y0 = y1)))) \/ (exists y1 : real, (~ (real_le y0 y1)) /\ ((~ (real_le y1 y0)) \/ (y0 = y1))).
Definition term112 := fun y0 : real => ((fun y1 : real => exists y2 : real, (real_le y1 y2) /\ ((real_le y2 y1) /\ (~ (y1 = y2)))) y0) \/ ((fun y1 : real => exists y2 : real, (~ (real_le y1 y2)) /\ ((~ (real_le y2 y1)) \/ (y1 = y2))) y0).
Definition term239 (x0 : real) := (real_le x0 x0) -> False.
Definition term229 (x0 : real) (x1 : real) := (real_le x0 x1) -> False.
Definition term97 (x0 : real) := or (exists y0 : real, (real_le x0 y0) /\ ((real_le y0 x0) /\ (~ (x0 = y0)))).
Definition term119 := or (exists y0 : real, exists y1 : real, (real_le y0 y1) /\ ((real_le y1 y0) /\ (~ (y0 = y1)))).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term27 := (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1)))) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> False.
Definition term57 (x0 : real) (x1 : real) := (real_le x0 x1) /\ ((real_le x1 x0) /\ (~ (x0 = x1))).
Definition term235 (x0 : real) (x1 : real) := imp (x0 = x1).
Definition term102 := fun y0 : real => (exists y1 : real, (real_le y0 y1) /\ ((real_le y1 y0) /\ (~ (y0 = y1)))) \/ (exists y1 : real, (~ (real_le y0 y1)) /\ ((~ (real_le y1 y0)) \/ (y0 = y1))).
Definition term217 (x0 : real) (x1 : real) := (~ (~ (real_le x1 x0))) /\ (~ (~ (real_le x0 x1))).
Definition term159 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0)).
Definition term168 := forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0).
Definition term145 (x0 : real) := forall y0 : real, ((fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0).
Definition term228 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) -> real_le x0 x1.
Definition term105 := (exists y0 : real, (fun y1 : real => exists y2 : real, (real_le y1 y2) /\ ((real_le y2 y1) /\ (~ (y1 = y2)))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (~ (real_le y1 y2)) /\ ((~ (real_le y2 y1)) \/ (y1 = y2))) y0).
Definition term83 (x0 : real) := (exists y0 : real, (fun y1 : real => (real_le x0 y1) /\ ((real_le y1 x0) /\ (~ (x0 = y1)))) y0) \/ (exists y0 : real, (fun y1 : real => (~ (real_le x0 y1)) /\ ((~ (real_le y1 x0)) \/ (x0 = y1))) y0).
Definition term194 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0)) x1.
Definition term37 := imp (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((~ (real_le y1 y0)) \/ (y0 = y1)))).
Definition term226 (x0 : Prop) := x0 -> ~ x0.
Definition term170 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1)).
Definition term150 (x0 : real) (x1 : real) := ((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1)).
Definition term164 (x0 : real) := forall y0 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0).
Definition term52 (x0 : real) (x1 : real) := (~ (~ (real_le x1 x0))) /\ (~ (x0 = x1)).
Definition term234 (x0 : real) (x1 : real) := imp (~ (~ (x0 = x1))).
Definition term121 := exists y0 : real, (fun y1 : real => exists y2 : real, (~ (real_le y1 y2)) /\ ((~ (real_le y2 y1)) \/ (y1 = y2))) y0.
Definition term116 := exists y0 : real, (fun y1 : real => exists y2 : real, (real_le y1 y2) /\ ((real_le y2 y1) /\ (~ (y1 = y2)))) y0.
Definition term127 (x0 : real) := @eq Prop ((exists y0 : real, (real_le x0 y0) /\ ((real_le y0 x0) /\ (~ (x0 = y0)))) \/ (exists y0 : real, (~ (real_le x0 y0)) /\ ((~ (real_le y0 x0)) \/ (x0 = y0)))).
Definition term126 (x0 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => (real_le x0 y1) /\ ((real_le y1 x0) /\ (~ (x0 = y1)))) y0) \/ (exists y0 : real, (fun y1 : real => (~ (real_le x0 y1)) /\ ((~ (real_le y1 x0)) \/ (x0 = y1))) y0)).
Definition term125 := @eq Prop ((exists y0 : real, exists y1 : real, (real_le y0 y1) /\ ((real_le y1 y0) /\ (~ (y0 = y1)))) \/ (exists y0 : real, exists y1 : real, (~ (real_le y0 y1)) /\ ((~ (real_le y1 y0)) \/ (y0 = y1)))).
Definition term124 := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, (real_le y1 y2) /\ ((real_le y2 y1) /\ (~ (y1 = y2)))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (~ (real_le y1 y2)) /\ ((~ (real_le y2 y1)) \/ (y1 = y2))) y0)).
