Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term135 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) \/ (real_le x0 x1).
Definition term130 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> real_le x0 x1.
Definition term157 (x0 : real) (x1 : real) := (~ ((~ (real_le x0 x1)) \/ (real_lt x0 x1))) -> x0 = x1.
Definition term32 (x0 : real -> Prop) := ~ (all x0).
Definition term185 := (~ False) -> False.
Definition term11 := imp (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)).
Definition term62 (x0 : real) (x1 : real) := ((real_le x0 x1) \/ ((~ (real_lt x0 x1)) /\ (~ (x0 = x1)))) /\ ((~ (real_le x0 x1)) \/ ((real_lt x0 x1) \/ (x0 = x1))).
Definition term146 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) \/ (x0 = x1).
Definition term162 (x0 : Prop) := ~ (~ x0).
Definition term108 := and (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ ((~ (real_lt y0 y1)) /\ (~ (y0 = y1)))).
Definition term30 (x0 : real) (x1 : real) := (real_le x0 x1) /\ (~ (real_le (sqrt x0) (sqrt x1))).
Definition term25 (x0 : real) (x1 : real) := (real_le x0 x1) -> real_le (sqrt x0) (sqrt x1).
Definition term86 (x0 : real) := and (forall y0 : real, (real_le x0 y0) \/ ((~ (real_lt x0 y0)) /\ (~ (x0 = y0)))).
Definition term163 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term124 (x0 : real) (x1 : real) := ~ (real_le (sqrt x0) (sqrt x1)).
Definition term98 (x0 : real) := and ((fun y0 : real => forall y1 : real, (real_le y0 y1) \/ ((~ (real_lt y0 y1)) /\ (~ (y0 = y1)))) x0).
Definition term40 (x0 : real) := exists y0 : real, (real_le x0 y0) /\ (~ (real_le (sqrt x0) (sqrt y0))).
Definition term179 (x0 : real) (x1 : real) := ~ ((sqrt x0) = (sqrt x1)).
Definition term107 := and (forall y0 : real, (fun y1 : real => forall y2 : real, (real_le y1 y2) \/ ((~ (real_lt y1 y2)) /\ (~ (y1 = y2)))) y0).
Definition term85 (x0 : real) := and (forall y0 : real, (fun y1 : real => (real_le x0 y1) \/ ((~ (real_lt x0 y1)) /\ (~ (x0 = y1)))) y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term133 (x0 : real) (x1 : real) := (real_le (sqrt x0) (sqrt x1)) -> ~ (real_le (sqrt x0) (sqrt x1)).
Definition term34 (x0 : real) := ~ (forall y0 : real, (real_le x0 y0) -> real_le (sqrt x0) (sqrt y0)).
Definition term183 (x0 : real) (x1 : real) := (~ (real_le (sqrt x0) (sqrt x1))) -> real_le (sqrt x0) (sqrt x1).
Definition term91 := fun y0 : real => (forall y1 : real, (real_le y0 y1) \/ ((~ (real_lt y0 y1)) /\ (~ (y0 = y1)))) /\ (forall y1 : real, (~ (real_le y0 y1)) \/ ((real_lt y0 y1) \/ (y0 = y1))).
Definition term54 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) /\ (~ (x0 = x1)).
Definition term112 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ ((~ (real_lt y0 y1)) /\ (~ (y0 = y1)))) /\ (forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) \/ ((real_lt y0 y1) \/ (y0 = y1))).
Definition term37 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_le x0 y0) -> real_le (sqrt x0) (sqrt y0)) x1).
Definition term169 (x0 : real) (x1 : real) := ((real_le x0 x1) /\ (~ (real_lt x0 x1))) -> x0 = x1.
Definition term148 (x0 : real) (x1 : real) := or (real_lt x0 x1).
Definition term137 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term143 (x0 : real) (x1 : real) := (real_lt x0 x1) -> ~ (real_lt x0 x1).
Definition term94 := (forall y0 : real, (fun y1 : real => forall y2 : real, (real_le y1 y2) \/ ((~ (real_lt y1 y2)) /\ (~ (y1 = y2)))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ ((real_lt y1 y2) \/ (y1 = y2))) y0).
Definition term72 (x0 : real) := (forall y0 : real, (fun y1 : real => (real_le x0 y1) \/ ((~ (real_lt x0 y1)) /\ (~ (x0 = y1)))) y0) /\ (forall y0 : real, (fun y1 : real => (~ (real_le x0 y1)) \/ ((real_lt x0 y1) \/ (x0 = y1))) y0).
Definition term89 (x0 : real) := forall y0 : real, (~ (real_le x0 y0)) \/ ((real_lt x0 y0) \/ (x0 = y0)).
Definition term166 (x0 : real) (x1 : real) := (real_le x0 x1) /\ (~ (real_lt x0 x1)).
Definition term132 (x0 : Prop) := (~ x0) -> x0.
Definition term136 (x0 : real) (x1 : real) := @eq Prop ((real_le x0 x1) \/ (~ (real_lt x0 x1))).
Definition term5 := ((~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) -> False.
Definition term109 := fun y0 : real => (fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ ((real_lt y1 y2) \/ (y1 = y2))) y0.
Definition term104 := fun y0 : real => (fun y1 : real => forall y2 : real, (real_le y1 y2) \/ ((~ (real_lt y1 y2)) /\ (~ (y1 = y2)))) y0.
Definition term138 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> ~ (real_lt x0 x1).
Definition term159 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term180 (x0 : real) (x1 : real) := (~ (~ (x0 = x1))) -> real_le x0 x1.
Definition term178 (x0 : real) (x1 : real) := (~ ((sqrt x0) = (sqrt x1))) -> (sqrt x0) = (sqrt x1).
Definition term160 (x0 : real) (x1 : real) := ~ ((~ (real_le x0 x1)) \/ (real_lt x0 x1)).
Definition term129 (x0 : real) (x1 : real) := (~ (x0 = x1)) \/ ((sqrt x0) = (sqrt x1)).
Definition term151 (x0 : real) (x1 : real) := @eq Prop ((~ (real_le x0 x1)) \/ ((real_lt x0 x1) \/ (x0 = x1))).
Definition term119 := forall y0 : real, forall y1 : real, ((real_le y0 y1) \/ (~ (real_lt y0 y1))) /\ ((real_le y0 y1) \/ (~ (y0 = y1))).
Definition term111 := forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) \/ ((real_lt y0 y1) \/ (y0 = y1)).
Definition term106 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ ((~ (real_lt y0 y1)) /\ (~ (y0 = y1))).
Definition term66 := forall y0 : real, forall y1 : real, ((real_le y0 y1) \/ ((~ (real_lt y0 y1)) /\ (~ (y0 = y1)))) /\ ((~ (real_le y0 y1)) \/ ((real_lt y0 y1) \/ (y0 = y1))).
Definition term52 := forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) \/ (real_lt (sqrt y0) (sqrt y1)).
Definition term24 := forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1).
Definition term10 := forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1)).
Definition term1 := forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1).
Definition term140 (x0 : real) (x1 : real) := ~ (real_lt (sqrt x0) (sqrt x1)).
Definition term36 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) -> real_le (sqrt x0) (sqrt y0)) x1.
Definition term46 := exists y0 : real, exists y1 : real, (real_le y0 y1) /\ (~ (real_le (sqrt y0) (sqrt y1))).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term12 := (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) -> False.
Definition term170 (x0 : real) (x1 : real) := (~ (x0 = x1)) -> x0 = x1.
Definition term144 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term15 := (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))).
Definition term173 (x0 : real) (x1 : real) := @eq Prop (((sqrt x0) = (sqrt x1)) \/ (~ (x0 = x1))).
Definition term41 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_le y1 y2) -> real_le (sqrt y1) (sqrt y2)) y0).
Definition term35 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_le x0 y1) -> real_le (sqrt x0) (sqrt y1)) y0).
Definition term152 (x0 : real) (x1 : real) := @eq Prop ((x0 = x1) \/ ((real_lt x0 x1) \/ (~ (real_le x0 x1)))).
Definition term87 (x0 : real) := fun y0 : real => (fun y1 : real => (~ (real_le x0 y1)) \/ ((real_lt x0 y1) \/ (x0 = y1))) y0.
Definition term82 (x0 : real) := fun y0 : real => (fun y1 : real => (real_le x0 y1) \/ ((~ (real_lt x0 y1)) /\ (~ (x0 = y1)))) y0.
Definition term50 (x0 : real) := forall y0 : real, (~ (real_lt x0 y0)) \/ (real_lt (sqrt x0) (sqrt y0)).
Definition term44 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_le y1 y2) -> real_le (sqrt y1) (sqrt y2)) y0).
Definition term103 := @eq Prop (forall y0 : real, (forall y1 : real, (real_le y0 y1) \/ ((~ (real_lt y0 y1)) /\ (~ (y0 = y1)))) /\ (forall y1 : real, (~ (real_le y0 y1)) \/ ((real_lt y0 y1) \/ (y0 = y1)))).
Definition term102 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, (real_le y1 y2) \/ ((~ (real_lt y1 y2)) /\ (~ (y1 = y2)))) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ ((real_lt y1 y2) \/ (y1 = y2))) y0)).
Definition term81 (x0 : real) := @eq Prop (forall y0 : real, ((real_le x0 y0) \/ ((~ (real_lt x0 y0)) /\ (~ (x0 = y0)))) /\ ((~ (real_le x0 y0)) \/ ((real_lt x0 y0) \/ (x0 = y0)))).
Definition term80 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (real_le x0 y1) \/ ((~ (real_lt x0 y1)) /\ (~ (x0 = y1)))) y0) /\ ((fun y1 : real => (~ (real_le x0 y1)) \/ ((real_lt x0 y1) \/ (x0 = y1))) y0)).
Definition term171 (x0 : real) (x1 : real) := ((sqrt x0) = (sqrt x1)) \/ (~ (x0 = x1)).
Definition term45 := fun y0 : real => exists y1 : real, (real_le y0 y1) /\ (~ (real_le (sqrt y0) (sqrt y1))).
Definition term118 := fun y0 : real => forall y1 : real, ((real_le y0 y1) \/ (~ (real_lt y0 y1))) /\ ((real_le y0 y1) \/ (~ (y0 = y1))).
Definition term96 := fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ ((real_lt y0 y1) \/ (y0 = y1)).
Definition term95 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ ((~ (real_lt y0 y1)) /\ (~ (y0 = y1))).
Definition term65 := fun y0 : real => forall y1 : real, ((real_le y0 y1) \/ ((~ (real_lt y0 y1)) /\ (~ (y0 = y1)))) /\ ((~ (real_le y0 y1)) \/ ((real_lt y0 y1) \/ (y0 = y1))).
Definition term51 := fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (real_lt (sqrt y0) (sqrt y1)).
Definition term28 := fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1).
Definition term23 := fun y0 : real => forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1).
Definition term19 := fun y0 : real => forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1)).
Definition term8 := (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) -> False.
Definition term167 (x0 : real) (x1 : real) := imp (~ ((~ (real_le x0 x1)) \/ (real_lt x0 x1))).
Definition term29 (x0 : real) (x1 : real) := ~ ((real_le x0 x1) -> real_le (sqrt x0) (sqrt x1)).
Definition term39 (x0 : real) := fun y0 : real => (real_le x0 y0) /\ (~ (real_le (sqrt x0) (sqrt y0))).
Definition term115 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term9 := ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))).
Definition term3 := ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)).
Definition term145 (x0 : real) (x1 : real) := (real_lt x0 x1) \/ ((~ (real_le x0 x1)) \/ (x0 = x1)).
Definition term114 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term56 (x0 : real) (x1 : real) := or (real_le x0 x1).
Definition term161 (x0 : real) (x1 : real) := (~ (~ (real_le x0 x1))) /\ (~ (real_lt x0 x1)).
Definition term84 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ ((~ (real_lt x0 y0)) /\ (~ (x0 = y0))).
Definition term63 (x0 : real) := fun y0 : real => ((real_le x0 y0) \/ ((~ (real_lt x0 y0)) /\ (~ (x0 = y0)))) /\ ((~ (real_le x0 y0)) \/ ((real_lt x0 y0) \/ (x0 = y0))).
Definition term77 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_le x0 y0)) \/ ((real_lt x0 y0) \/ (x0 = y0))) x1.
Definition term158 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term90 (x0 : real) := (forall y0 : real, (real_le x0 y0) \/ ((~ (real_lt x0 y0)) /\ (~ (x0 = y0)))) /\ (forall y0 : real, (~ (real_le x0 y0)) \/ ((real_lt x0 y0) \/ (x0 = y0))).
Definition term117 (x0 : real) := forall y0 : real, ((real_le x0 y0) \/ (~ (real_lt x0 y0))) /\ ((real_le x0 y0) \/ (~ (x0 = y0))).
Definition term43 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) x0).
Definition term149 (x0 : real) (x1 : real) := (real_lt x0 x1) \/ ((x0 = x1) \/ (~ (real_le x0 x1))).
Definition term154 (x0 : real) (x1 : real) := (real_lt x0 x1) \/ (~ (real_le x0 x1)).
Definition term121 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_lt x0 y0)) \/ (real_lt (sqrt x0) (sqrt y0))) x1.
Definition term75 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ ((~ (real_lt x0 y0)) /\ (~ (x0 = y0)))) x1.
Definition term6 := (((~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) -> False.
Definition term139 (x0 : real) (x1 : real) := (~ (real_le (sqrt x0) (sqrt x1))) -> ~ (real_lt (sqrt x0) (sqrt x1)).
Definition term31 (x0 : real) (x1 : real) := real_le (sqrt x0) (sqrt x1).
Definition term181 (x0 : real) (x1 : real) := (x0 = x1) -> real_le x0 x1.
Definition term26 (x0 : real) := fun y0 : real => (real_le x0 y0) -> real_le (sqrt x0) (sqrt y0).
Definition term33 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term69 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term122 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_le y0 y1) \/ (~ (real_lt y0 y1))) /\ ((real_le y0 y1) \/ (~ (y0 = y1)))) x0.
Definition term120 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (real_lt (sqrt y0) (sqrt y1))) x0.
Definition term99 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ ((real_lt y0 y1) \/ (y0 = y1))) x0.
Definition term97 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ ((~ (real_lt y0 y1)) /\ (~ (y0 = y1)))) x0.
Definition term42 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) x0.
Definition term49 (x0 : real) := fun y0 : real => (~ (real_lt x0 y0)) \/ (real_lt (sqrt x0) (sqrt y0)).
Definition term150 (x0 : real) (x1 : real) := (x0 = x1) \/ ((real_lt x0 x1) \/ (~ (real_le x0 x1))).
Definition term2 := (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1))) -> False.
Definition term88 (x0 : real) := forall y0 : real, (fun y1 : real => (~ (real_le x0 y1)) \/ ((real_lt x0 y1) \/ (x0 = y1))) y0.
Definition term83 (x0 : real) := forall y0 : real, (fun y1 : real => (real_le x0 y1) \/ ((~ (real_lt x0 y1)) /\ (~ (x0 = y1)))) y0.
Definition term155 (x0 : real) (x1 : real) := or (x0 = x1).
Definition term47 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) \/ (real_lt (sqrt x0) (sqrt x1)).
Definition term59 (x0 : real) (x1 : real) := and ((real_le x0 x1) \/ (~ ((real_lt x0 x1) \/ (x0 = x1)))).
Definition term101 := fun y0 : real => ((fun y1 : real => forall y2 : real, (real_le y1 y2) \/ ((~ (real_lt y1 y2)) /\ (~ (y1 = y2)))) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ ((real_lt y1 y2) \/ (y1 = y2))) y0).
Definition term168 (x0 : real) (x1 : real) := imp ((real_le x0 x1) /\ (~ (real_lt x0 x1))).
Definition term7 := (((~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) -> False) -> ((~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) -> False.
Definition term78 (x0 : real) (x1 : real) := ((fun y0 : real => (real_le x0 y0) \/ ((~ (real_lt x0 y0)) /\ (~ (x0 = y0)))) x1) /\ ((fun y0 : real => (~ (real_le x0 y0)) \/ ((real_lt x0 y0) \/ (x0 = y0))) x1).
Definition term164 (x0 : real) (x1 : real) := and (~ (~ (real_le x0 x1))).
Definition term74 (x0 : real) := fun y0 : real => (~ (real_le x0 y0)) \/ ((real_lt x0 y0) \/ (x0 = y0)).
Definition term17 (x0 : real) := fun y0 : real => (real_le x0 y0) = ((real_lt x0 y0) \/ (x0 = y0)).
Definition term116 (x0 : real) := fun y0 : real => ((real_le x0 y0) \/ (~ (real_lt x0 y0))) /\ ((real_le x0 y0) \/ (~ (x0 = y0))).
Definition term60 (x0 : real) (x1 : real) := and ((real_le x0 x1) \/ ((~ (real_lt x0 x1)) /\ (~ (x0 = x1)))).
Definition term142 (x0 : real) (x1 : real) := (~ (real_lt (sqrt x0) (sqrt x1))) -> ~ (real_lt x0 x1).
Definition term153 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) \/ (real_lt x0 x1).
Definition term123 (x0 : real) (x1 : real) := (fun y0 : real => ((real_le x0 y0) \/ (~ (real_lt x0 y0))) /\ ((real_le x0 y0) \/ (~ (x0 = y0)))) x1.
Definition term27 (x0 : real) := forall y0 : real, (real_le x0 y0) -> real_le (sqrt x0) (sqrt y0).
Definition term22 (x0 : real) := forall y0 : real, (real_lt x0 y0) -> real_lt (sqrt x0) (sqrt y0).
Definition term131 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term58 (x0 : real) (x1 : real) := (real_le x0 x1) \/ ((~ (real_lt x0 x1)) /\ (~ (x0 = x1))).
Definition term57 (x0 : real) (x1 : real) := (real_le x0 x1) \/ (~ ((real_lt x0 x1) \/ (x0 = x1))).
Definition term172 (x0 : real) (x1 : real) := @eq Prop ((~ (x0 = x1)) \/ ((sqrt x0) = (sqrt x1))).
Definition term92 := forall y0 : real, (forall y1 : real, (real_le y0 y1) \/ ((~ (real_lt y0 y1)) /\ (~ (y0 = y1)))) /\ (forall y1 : real, (~ (real_le y0 y1)) \/ ((real_lt y0 y1) \/ (y0 = y1))).
Definition term127 (x0 : real) (x1 : real) := (x0 = x1) -> (sqrt x0) = (sqrt x1).
Definition term126 (x0 : real) (x1 : real) := (real_le x0 x1) \/ (~ (x0 = x1)).
Definition term125 (x0 : real) (x1 : real) := (real_le x0 x1) \/ (~ (real_lt x0 x1)).
Definition term61 (x0 : real) (x1 : real) := ((real_le x0 x1) \/ (~ ((real_lt x0 x1) \/ (x0 = x1)))) /\ ((~ (real_le x0 x1)) \/ ((real_lt x0 x1) \/ (x0 = x1))).
Definition term48 (x0 : real) (x1 : real) := real_lt (sqrt x0) (sqrt x1).
Definition term16 (x0 : real) (x1 : real) := (real_lt x0 x1) \/ (x0 = x1).
Definition term141 (x0 : real) (x1 : real) := (real_lt (sqrt x0) (sqrt x1)) -> ~ (real_lt (sqrt x0) (sqrt x1)).
Definition term73 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ ((~ (real_lt x0 y0)) /\ (~ (x0 = y0))).
Definition term110 := forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ ((real_lt y1 y2) \/ (y1 = y2))) y0.
Definition term105 := forall y0 : real, (fun y1 : real => forall y2 : real, (real_le y1 y2) \/ ((~ (real_lt y1 y2)) /\ (~ (y1 = y2)))) y0.
Definition term100 (x0 : real) := ((fun y0 : real => forall y1 : real, (real_le y0 y1) \/ ((~ (real_lt y0 y1)) /\ (~ (y0 = y1)))) x0) /\ ((fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ ((real_lt y0 y1) \/ (y0 = y1))) x0).
Definition term13 := (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))).
Definition term165 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term128 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term79 (x0 : real) := fun y0 : real => ((fun y1 : real => (real_le x0 y1) \/ ((~ (real_lt x0 y1)) /\ (~ (x0 = y1)))) y0) /\ ((fun y1 : real => (~ (real_le x0 y1)) \/ ((real_lt x0 y1) \/ (x0 = y1))) y0).
Definition term55 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) \/ ((real_lt x0 x1) \/ (x0 = x1)).
Definition term64 (x0 : real) := forall y0 : real, ((real_le x0 y0) \/ ((~ (real_lt x0 y0)) /\ (~ (x0 = y0)))) /\ ((~ (real_le x0 y0)) \/ ((real_lt x0 y0) \/ (x0 = y0))).
Definition term38 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_le x0 y1) -> real_le (sqrt x0) (sqrt y1)) y0).
Definition term70 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term156 (x0 : real) (x1 : real) := (x0 = x1) \/ ((~ (real_le x0 x1)) \/ (real_lt x0 x1)).
Definition term113 (x0 : real) (x1 : real) := ((real_le x0 x1) \/ (~ (real_lt x0 x1))) /\ ((real_le x0 x1) \/ (~ (x0 = x1))).
Definition term18 (x0 : real) := forall y0 : real, (real_le x0 y0) = ((real_lt x0 y0) \/ (x0 = y0)).
Definition term182 (x0 : real) (x1 : real) := ((sqrt x0) = (sqrt x1)) -> real_le (sqrt x0) (sqrt x1).
Definition term174 (x0 : real) (x1 : real) := (~ (~ (x0 = x1))) -> (sqrt x0) = (sqrt x1).
Definition term175 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term53 (x0 : real) (x1 : real) := ~ ((real_lt x0 x1) \/ (x0 = x1)).
Definition term76 (x0 : real) (x1 : real) := and ((fun y0 : real => (real_le x0 y0) \/ ((~ (real_lt x0 y0)) /\ (~ (x0 = y0)))) x1).
Definition term20 (x0 : real) (x1 : real) := (real_lt x0 x1) -> real_lt (sqrt x0) (sqrt x1).
Definition term184 (x0 : real) (x1 : real) := (real_le (sqrt x0) (sqrt x1)) -> False.
Definition term4 := (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1))) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) -> False.
Definition term177 (x0 : real) (x1 : real) := imp (x0 = x1).
Definition term147 (x0 : real) (x1 : real) := (x0 = x1) \/ (~ (real_le x0 x1)).
Definition term21 (x0 : real) := fun y0 : real => (real_lt x0 y0) -> real_lt (sqrt x0) (sqrt y0).
Definition term93 := forall y0 : real, ((fun y1 : real => forall y2 : real, (real_le y1 y2) \/ ((~ (real_lt y1 y2)) /\ (~ (y1 = y2)))) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_le y1 y2)) \/ ((real_lt y1 y2) \/ (y1 = y2))) y0).
Definition term71 (x0 : real) := forall y0 : real, ((fun y1 : real => (real_le x0 y1) \/ ((~ (real_lt x0 y1)) /\ (~ (x0 = y1)))) y0) /\ ((fun y1 : real => (~ (real_le x0 y1)) \/ ((real_lt x0 y1) \/ (x0 = y1))) y0).
Definition term14 := imp (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1))).
Definition term134 (x0 : Prop) := x0 -> ~ x0.
Definition term176 (x0 : real) (x1 : real) := imp (~ (~ (x0 = x1))).
