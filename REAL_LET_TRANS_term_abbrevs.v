Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term142 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> real_le x0 x1.
Definition term43 (x0 : real -> Prop) := ~ (all x0).
Definition term171 := (~ False) -> False.
Definition term87 (x0 : real) := fun y0 : real => ((real_lt y0 x0) \/ (real_le x0 y0)) /\ ((~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))).
Definition term18 := imp (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2).
Definition term166 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (real_le x0 x2)) \/ (real_le x1 x2))).
Definition term67 (x0 : real) (x1 : real) (x2 : real) := or (~ ((real_le x0 x1) /\ (real_le x1 x2))).
Definition term150 (x0 : Prop) := ~ (~ x0).
Definition term157 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (real_le x2 x0)) \/ (real_le x1 x0))) -> ~ (real_le x1 x2).
Definition term140 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x1 x0)) \/ ((~ (real_le x0 x2)) \/ (real_le x1 x2)).
Definition term84 (x0 : real) (x1 : real) := and ((real_lt x1 x0) \/ (real_le x0 x1)).
Definition term132 := and (forall y0 : real, forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)).
Definition term110 (x0 : real) := and (forall y0 : real, (real_lt y0 x0) \/ (real_le x0 y0)).
Definition term139 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0)) x2.
Definition term78 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term122 (x0 : real) := and ((fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) x0).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term131 := and (forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0).
Definition term109 (x0 : real) := and (forall y0 : real, (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term45 (x0 : real) (x1 : real) := ~ (forall y0 : real, ((real_le x1 x0) /\ (real_lt x0 y0)) -> real_lt x1 y0).
Definition term85 (x0 : real) (x1 : real) := ((real_lt x1 x0) \/ (~ (~ (real_le x0 x1)))) /\ ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))).
Definition term115 := fun y0 : real => (forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term99 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0)) x1.
Definition term154 (x0 : real) (x1 : real) := (real_lt x1 x0) -> ~ (real_le x0 x1).
Definition term136 := (forall y0 : real, forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y0 : real, forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term144 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) -> real_lt x0 x1.
Definition term170 (x0 : real) (x1 : real) := (real_lt x0 x1) -> False.
Definition term80 (x0 : real) (x1 : real) := or (real_lt x0 x1).
Definition term148 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term118 := (forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0).
Definition term96 (x0 : real) := (forall y0 : real, (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ (forall y0 : real, (fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0).
Definition term70 (x0 : real) (x1 : real) (x2 : real) := ((~ (real_le x1 x0)) \/ (~ (real_le x0 x2))) \/ (real_le x1 x2).
Definition term143 (x0 : Prop) := (~ x0) -> x0.
Definition term12 := ((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term147 (x0 : real) (x1 : real) := @eq Prop ((~ (real_le x1 x0)) \/ (~ (real_lt x0 x1))).
Definition term146 (x0 : real) (x1 : real) := @eq Prop ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))).
Definition term133 := fun y0 : real => (fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0.
Definition term128 := fun y0 : real => (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0.
Definition term160 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term168 (x0 : real) (x1 : real) (x2 : real) := ((real_le x2 x0) /\ (~ (real_le x1 x0))) -> ~ (real_le x1 x2).
Definition term35 (x0 : real) (x1 : real) := fun y0 : real => ((real_le x1 x0) /\ (real_lt x0 y0)) -> real_lt x1 y0.
Definition term40 (x0 : real) (x1 : real) (x2 : real) := ~ (((real_le x1 x0) /\ (real_lt x0 x2)) -> real_lt x1 x2).
Definition term135 := forall y0 : real, forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1)).
Definition term130 := forall y0 : real, forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1).
Definition term90 := forall y0 : real, forall y1 : real, ((real_lt y1 y0) \/ (real_le y0 y1)) /\ ((~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term77 := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2).
Definition term75 (x0 : real) := forall y0 : real, forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1).
Definition term38 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_lt y0 y1)) -> real_lt x0 y1.
Definition term33 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term31 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term17 := forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1)).
Definition term8 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2.
Definition term64 := exists y0 : real, exists y1 : real, exists y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) /\ (~ (real_lt y0 y2)).
Definition term58 (x0 : real) := exists y0 : real, exists y1 : real, ((real_le x0 y0) /\ (real_lt y0 y1)) /\ (~ (real_lt x0 y1)).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term19 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term81 (x0 : real) (x1 : real) := (real_lt x1 x0) \/ (~ (~ (real_le x0 x1))).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term27 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_le x0 x2)) -> real_le x1 x2.
Definition term41 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_lt x0 x2)) /\ (~ (real_lt x1 x2)).
Definition term22 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> ~ (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))).
Definition term108 (x0 : real) := forall y0 : real, (real_lt y0 x0) \/ (real_le x0 y0).
Definition term59 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3) y0).
Definition term53 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, ((real_le x0 y1) /\ (real_lt y1 y2)) -> real_lt x0 y2) y0).
Definition term46 (x0 : real) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => ((real_le x1 x0) /\ (real_lt x0 y1)) -> real_lt x1 y1) y0).
Definition term62 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_lt y2 y3)) -> real_lt y1 y3) y0).
Definition term56 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, ((real_le x0 y1) /\ (real_lt y1 y2)) -> real_lt x0 y2) y0).
Definition term127 := @eq Prop (forall y0 : real, (forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1)))).
Definition term126 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0)).
Definition term105 (x0 : real) := @eq Prop (forall y0 : real, ((real_lt y0 x0) \/ (real_le x0 y0)) /\ ((~ (real_lt y0 x0)) \/ (~ (real_le x0 y0)))).
Definition term104 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ ((fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0)).
Definition term57 (x0 : real) := fun y0 : real => exists y1 : real, ((real_le x0 y0) /\ (real_lt y0 y1)) /\ (~ (real_lt x0 y1)).
Definition term79 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) \/ (~ (real_le x0 x1)).
Definition term161 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (real_le x0 x2)) \/ (real_le x1 x2)).
Definition term89 := fun y0 : real => forall y1 : real, ((real_lt y1 y0) \/ (real_le y0 y1)) /\ ((~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term169 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) -> real_lt x0 x1.
Definition term15 := (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term52 (x0 : real) := ~ (forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_lt y0 y1)) -> real_lt x0 y1).
Definition term16 := ~ (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))).
Definition term10 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2).
Definition term141 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term51 (x0 : real) (x1 : real) := exists y0 : real, ((real_le x1 x0) /\ (real_lt x0 y0)) /\ (~ (real_lt x1 y0)).
Definition term155 (x0 : real) (x1 : real) := (real_le x0 x1) -> ~ (real_le x0 x1).
Definition term159 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term114 (x0 : real) := (forall y0 : real, (real_lt y0 x0) \/ (real_le x0 y0)) /\ (forall y0 : real, (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))).
Definition term88 (x0 : real) := forall y0 : real, ((real_lt y0 x0) \/ (real_le x0 y0)) /\ ((~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))).
Definition term69 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_le x1 x0) /\ (real_le x0 x2))) \/ (real_le x1 x2).
Definition term61 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) x0).
Definition term113 (x0 : real) := forall y0 : real, (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0)).
Definition term111 (x0 : real) := fun y0 : real => (fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0.
Definition term13 := (((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term119 := fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1).
Definition term74 (x0 : real) := fun y0 : real => forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1).
Definition term37 (x0 : real) := fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_lt y0 y1)) -> real_lt x0 y1.
Definition term30 (x0 : real) := fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term44 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term93 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term48 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => ((real_le x1 x0) /\ (real_lt x0 y0)) -> real_lt x1 y0) x2).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term153 (x0 : real) (x1 : real) := imp (real_lt x0 x1).
Definition term123 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))) x0.
Definition term121 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) x0.
Definition term68 (x0 : real) (x1 : real) (x2 : real) := or ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term9 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2)) -> False.
Definition term112 (x0 : real) := forall y0 : real, (fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0.
Definition term107 (x0 : real) := forall y0 : real, (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0.
Definition term47 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_le x1 x0) /\ (real_lt x0 y0)) -> real_lt x1 y0) x2.
Definition term125 := fun y0 : real => ((fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0).
Definition term149 (x0 : real) (x1 : real) := (~ (~ (real_lt x1 x0))) -> ~ (real_le x0 x1).
Definition term83 (x0 : real) (x1 : real) := and ((real_lt x1 x0) \/ (~ (~ (real_le x0 x1)))).
Definition term14 := (((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> ((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term102 (x0 : real) (x1 : real) := ((fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0)) x1) /\ ((fun y0 : real => (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))) x1).
Definition term138 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1)) x1.
Definition term54 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_lt y0 y1)) -> real_lt x0 y1) x1.
Definition term163 (x0 : real) (x1 : real) := and (~ (~ (real_le x0 x1))).
Definition term101 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))) x1.
Definition term72 (x0 : real) (x1 : real) := fun y0 : real => ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0).
Definition term25 (x0 : real) := forall y0 : real, (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term165 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) /\ (~ (real_le x1 x2)).
Definition term151 (x0 : real) (x1 : real) := ~ (~ (real_lt x0 x1)).
Definition term76 := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2).
Definition term39 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2.
Definition term32 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term55 (x0 : real) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_lt y0 y1)) -> real_lt x0 y1) x1).
Definition term63 := fun y0 : real => exists y1 : real, exists y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) /\ (~ (real_lt y0 y2)).
Definition term97 (x0 : real) := fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0).
Definition term23 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term145 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ (~ (real_lt x0 x1)).
Definition term116 := forall y0 : real, (forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term36 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_lt x0 y0)) -> real_lt x1 y0.
Definition term29 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term42 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_lt x1 x2).
Definition term134 := forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0.
Definition term129 := forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0.
Definition term24 (x0 : real) := fun y0 : real => (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term82 (x0 : real) (x1 : real) := (real_lt x1 x0) \/ (real_le x0 x1).
Definition term124 (x0 : real) := ((fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) x0) /\ ((fun y0 : real => forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))) x0).
Definition term20 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> ~ (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))).
Definition term164 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term103 (x0 : real) := fun y0 : real => ((fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ ((fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0).
Definition term106 (x0 : real) := fun y0 : real => (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0.
Definition term71 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le x1 x2).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term49 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => ((real_le x1 x0) /\ (real_lt x0 y1)) -> real_lt x1 y1) y0).
Definition term94 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term98 (x0 : real) := fun y0 : real => (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0)).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term28 (x0 : real) (x1 : real) := fun y0 : real => ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term100 (x0 : real) (x1 : real) := and ((fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0)) x1).
Definition term65 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_le x0 x1) /\ (real_le x1 x2)).
Definition term158 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x2)) \/ (real_le x1 x2).
Definition term34 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_lt x0 x2)) -> real_lt x1 x2.
Definition term137 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2)) x0.
Definition term60 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) x0.
Definition term11 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2)) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term117 := forall y0 : real, ((fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0).
Definition term95 (x0 : real) := forall y0 : real, ((fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ ((fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0).
Definition term21 := imp (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2)).
Definition term156 (x0 : Prop) := x0 -> ~ x0.
Definition term120 := fun y0 : real => forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1)).
Definition term26 := fun y0 : real => forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1)).
Definition term86 (x0 : real) (x1 : real) := ((real_lt x1 x0) \/ (real_le x0 x1)) /\ ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))).
Definition term167 (x0 : real) (x1 : real) (x2 : real) := imp ((real_le x0 x2) /\ (~ (real_le x1 x2))).
Definition term73 (x0 : real) (x1 : real) := forall y0 : real, ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0).
Definition term50 (x0 : real) (x1 : real) := fun y0 : real => ((real_le x1 x0) /\ (real_lt x0 y0)) /\ (~ (real_lt x1 y0)).
Definition term66 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ (~ (real_le x1 x2)).
Definition term162 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (real_le x0 x2))) /\ (~ (real_le x1 x2)).
Definition term152 (x0 : real) (x1 : real) := imp (~ (~ (real_lt x0 x1))).
