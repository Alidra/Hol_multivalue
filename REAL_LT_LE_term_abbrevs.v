Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term63 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt x0 y0) = ((real_le x0 y0) /\ (~ (x0 = y0)))) x1.
Definition term37 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term56 (x0 : real) (x1 : real) := ((real_lt x0 x1) /\ (~ ((real_le x0 x1) /\ (~ (x0 = x1))))) \/ ((~ (real_lt x0 x1)) /\ ((real_le x0 x1) /\ (~ (x0 = x1)))).
Definition term272 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> real_le x0 x1.
Definition term59 (x0 : real -> Prop) := ~ (all x0).
Definition term274 := (~ False) -> False.
Definition term193 (x0 : real) := fun y0 : real => ((real_lt y0 x0) \/ (real_le x0 y0)) /\ ((~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))).
Definition term21 := imp (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)).
Definition term18 := imp (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term55 (x0 : real) (x1 : real) := or ((real_lt x0 x1) /\ ((~ (real_le x0 x1)) \/ (x0 = x1))).
Definition term47 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) \/ (x0 = x1).
Definition term119 := (exists y0 : real, exists y1 : real, (real_lt y0 y1) /\ ((~ (real_le y0 y1)) \/ (y0 = y1))) \/ (exists y0 : real, exists y1 : real, (~ (real_lt y0 y1)) /\ ((real_le y0 y1) /\ (~ (y0 = y1)))).
Definition term263 (x0 : Prop) := ~ (~ x0).
Definition term190 (x0 : real) (x1 : real) := and ((real_lt x1 x0) \/ (real_le x0 x1)).
Definition term25 := (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))).
Definition term234 := and (forall y0 : real, forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)).
Definition term179 := and (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))).
Definition term212 (x0 : real) := and (forall y0 : real, (real_lt y0 x0) \/ (real_le x0 y0)).
Definition term157 (x0 : real) := and (forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))).
Definition term184 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term224 (x0 : real) := and ((fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) x0).
Definition term169 (x0 : real) := and ((fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) x0).
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term288 (x0 : real) (x1 : real) := ~ ((real_lt x1 x0) /\ (real_le x0 x1)).
Definition term124 (x0 : real) (x1 : real) := ~ ((real_le x1 x0) /\ (real_le x0 x1)).
Definition term23 := (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))).
Definition term32 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_le y0 x0).
Definition term66 (x0 : real) := fun y0 : real => ((real_lt x0 y0) /\ ((~ (real_le x0 y0)) \/ (x0 = y0))) \/ ((~ (real_lt x0 y0)) /\ ((real_le x0 y0) /\ (~ (x0 = y0)))).
Definition term81 (x0 : real) := fun y0 : real => (~ (real_lt x0 y0)) /\ ((real_le x0 y0) /\ (~ (x0 = y0))).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term233 := and (forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0).
Definition term211 (x0 : real) := and (forall y0 : real, (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0).
Definition term178 := and (forall y0 : real, (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0).
Definition term156 (x0 : real) := and (forall y0 : real, (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term311 (x0 : real) (x1 : real) := imp (~ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1)))).
Definition term61 (x0 : real) := ~ (forall y0 : real, (real_lt x0 y0) = ((real_le x0 y0) /\ (~ (x0 = y0)))).
Definition term191 (x0 : real) (x1 : real) := ((real_lt x1 x0) \/ (~ (~ (real_le x0 x1)))) /\ ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))).
Definition term133 (x0 : real) := fun y0 : real => (((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)).
Definition term50 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) /\ ((real_le x0 x1) /\ (~ (x0 = x1))).
Definition term217 := fun y0 : real => (forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term162 := fun y0 : real => (forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term315 (x0 : real) (x1 : real) := (x0 = x1) -> False.
Definition term105 (x0 : real) := or ((fun y0 : real => exists y1 : real, (real_lt y0 y1) /\ ((~ (real_le y0 y1)) \/ (y0 = y1))) x0).
Definition term30 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_le x0 x1).
Definition term201 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0)) x1.
Definition term267 (x0 : real) (x1 : real) := (real_lt x1 x0) -> ~ (real_le x0 x1).
Definition term313 (x0 : real) (x1 : real) := ((real_le x0 x1) /\ (real_le x1 x0)) -> x0 = x1.
Definition term238 := (forall y0 : real, forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y0 : real, forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term183 := (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y0 : real, forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term255 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) -> real_lt x0 x1.
Definition term64 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_lt x0 y0) = ((real_le x0 y0) /\ (~ (x0 = y0)))) x1).
Definition term186 (x0 : real) (x1 : real) := or (real_lt x0 x1).
Definition term261 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term293 (x0 : real) (x1 : real) := (real_lt x0 x1) -> ~ (real_lt x0 x1).
Definition term54 (x0 : real) (x1 : real) := or ((real_lt x0 x1) /\ (~ ((real_le x0 x1) /\ (~ (x0 = x1))))).
Definition term220 := (forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0).
Definition term198 (x0 : real) := (forall y0 : real, (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ (forall y0 : real, (fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0).
Definition term165 := (forall y0 : real, (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0).
Definition term142 (x0 : real) := (forall y0 : real, (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ (forall y0 : real, (fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0).
Definition term129 (x0 : real) (x1 : real) := ((~ (real_le x0 x1)) \/ (~ (real_le x1 x0))) \/ (x0 = x1).
Definition term277 (x0 : real) := (~ (x0 = x0)) -> x0 = x0.
Definition term296 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_lt x0 x1)).
Definition term126 (x0 : real) (x1 : real) := or (~ ((real_le x1 x0) /\ (real_le x0 x1))).
Definition term286 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term40 (x0 : real) (x1 : real) := (real_le x0 x1) /\ (~ (x0 = x1)).
Definition term257 (x0 : Prop) := (~ x0) -> x0.
Definition term128 (x0 : real) (x1 : real) := (~ ((real_le x0 x1) /\ (real_le x1 x0))) \/ (x0 = x1).
Definition term82 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt x0 y0) /\ ((~ (real_le x0 y0)) \/ (x0 = y0))) x1.
Definition term251 (x0 : real) := (fun y0 : real => real_lt y0 x0) x0.
Definition term260 (x0 : real) (x1 : real) := @eq Prop ((~ (real_le x1 x0)) \/ (~ (real_lt x0 x1))).
Definition term259 (x0 : real) (x1 : real) := @eq Prop ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))).
Definition term298 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ (x0 = x1).
Definition term235 := fun y0 : real => (fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0.
Definition term230 := fun y0 : real => (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0.
Definition term180 := fun y0 : real => (fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0.
Definition term175 := fun y0 : real => (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0.
Definition term53 (x0 : real) (x1 : real) := (real_lt x0 x1) /\ ((~ (real_le x0 x1)) \/ (x0 = x1)).
Definition term306 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term279 (x0 : real) (x1 : real) := (~ (~ (x1 = x0))) -> real_le x0 x1.
Definition term131 (x0 : real) (x1 : real) := (((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1))) /\ ((~ ((real_le x0 x1) /\ (real_le x1 x0))) \/ (x0 = x1)).
Definition term95 (x0 : real) := exists y0 : real, (fun y1 : real => (~ (real_lt x0 y1)) /\ ((real_le x0 y1) /\ (~ (x0 = y1)))) y0.
Definition term90 (x0 : real) := exists y0 : real, (fun y1 : real => (real_lt x0 y1) /\ ((~ (real_le x0 y1)) \/ (x0 = y1))) y0.
Definition term22 := (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term287 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term276 (x0 : real) := ~ (real_lt x0 x0).
Definition term243 := forall y0 : real, forall y1 : real, ((real_le y0 y1) \/ (~ (y0 = y1))) /\ ((real_le y1 y0) \/ (~ (y0 = y1))).
Definition term237 := forall y0 : real, forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1)).
Definition term232 := forall y0 : real, forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1).
Definition term196 := forall y0 : real, forall y1 : real, ((real_lt y1 y0) \/ (real_le y0 y1)) /\ ((~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term182 := forall y0 : real, forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1).
Definition term177 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1)).
Definition term136 := forall y0 : real, forall y1 : real, (((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term39 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term34 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term17 := forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1)).
Definition term8 := forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))).
Definition term134 (x0 : real) := forall y0 : real, (((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)).
Definition term249 (x0 : real) := fun y0 : real => real_lt y0 x0.
Definition term118 := exists y0 : real, exists y1 : real, (~ (real_lt y0 y1)) /\ ((real_le y0 y1) /\ (~ (y0 = y1))).
Definition term113 := exists y0 : real, exists y1 : real, (real_lt y0 y1) /\ ((~ (real_le y0 y1)) \/ (y0 = y1)).
Definition term73 := exists y0 : real, exists y1 : real, ((real_lt y0 y1) /\ ((~ (real_le y0 y1)) \/ (y0 = y1))) \/ ((~ (real_lt y0 y1)) /\ ((real_le y0 y1) /\ (~ (y0 = y1)))).
Definition term138 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term19 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term314 (x0 : real) (x1 : real) := (~ (x0 = x1)) -> x0 = x1.
Definition term114 := or (exists y0 : real, (fun y1 : real => exists y2 : real, (real_lt y1 y2) /\ ((~ (real_le y1 y2)) \/ (y1 = y2))) y0).
Definition term92 (x0 : real) := or (exists y0 : real, (fun y1 : real => (real_lt x0 y1) /\ ((~ (real_le x0 y1)) \/ (x0 = y1))) y0).
Definition term187 (x0 : real) (x1 : real) := (real_lt x1 x0) \/ (~ (~ (real_le x0 x1))).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term80 (x0 : real) := fun y0 : real => (real_lt x0 y0) /\ ((~ (real_le x0 y0)) \/ (x0 = y0)).
Definition term210 (x0 : real) := forall y0 : real, (real_lt y0 x0) \/ (real_le x0 y0).
Definition term304 (x0 : real) (x1 : real) := (~ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x0)))) -> x0 = x1.
Definition term48 (x0 : real) (x1 : real) := ~ ((real_le x0 x1) /\ (~ (x0 = x1))).
Definition term303 (x0 : real) (x1 : real) := @eq Prop ((x1 = x0) \/ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1)))).
Definition term285 (x0 : real) := ~ (real_le x0 x0).
Definition term254 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (~ (x0 = x1)).
Definition term68 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_lt y1 y2) = ((real_le y1 y2) /\ (~ (y1 = y2)))) y0).
Definition term62 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_lt x0 y1) = ((real_le x0 y1) /\ (~ (x0 = y1)))) y0).
Definition term106 (x0 : real) := (fun y0 : real => exists y1 : real, (~ (real_lt y0 y1)) /\ ((real_le y0 y1) /\ (~ (y0 = y1)))) x0.
Definition term104 (x0 : real) := (fun y0 : real => exists y1 : real, (real_lt y0 y1) /\ ((~ (real_le y0 y1)) \/ (y0 = y1))) x0.
Definition term51 (x0 : real) (x1 : real) := and (real_lt x0 x1).
Definition term71 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_lt y1 y2) = ((real_le y1 y2) /\ (~ (y1 = y2)))) y0).
Definition term229 := @eq Prop (forall y0 : real, (forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1)))).
Definition term228 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0)).
Definition term207 (x0 : real) := @eq Prop (forall y0 : real, ((real_lt y0 x0) \/ (real_le x0 y0)) /\ ((~ (real_lt y0 x0)) \/ (~ (real_le x0 y0)))).
Definition term206 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ ((fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0)).
Definition term174 := @eq Prop (forall y0 : real, (forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1))).
Definition term173 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0)).
Definition term152 (x0 : real) := @eq Prop (forall y0 : real, (((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0))).
Definition term151 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0)).
Definition term132 (x0 : real) (x1 : real) := (((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1))) /\ (((~ (real_le x0 x1)) \/ (~ (real_le x1 x0))) \/ (x0 = x1)).
Definition term185 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) \/ (~ (real_le x0 x1)).
Definition term125 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ (~ (real_le x0 x1)).
Definition term242 := fun y0 : real => forall y1 : real, ((real_le y0 y1) \/ (~ (y0 = y1))) /\ ((real_le y1 y0) \/ (~ (y0 = y1))).
Definition term195 := fun y0 : real => forall y1 : real, ((real_lt y1 y0) \/ (real_le y0 y1)) /\ ((~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term135 := fun y0 : real => forall y1 : real, (((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term43 := fun y0 : real => forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))).
Definition term284 (x0 : real) := (~ (real_le x0 x0)) -> real_le x0 x0.
Definition term15 := (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term294 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_lt x0 x1).
Definition term107 (x0 : real) := ((fun y0 : real => exists y1 : real, (real_lt y0 y1) /\ ((~ (real_le y0 y1)) \/ (y0 = y1))) x0) \/ ((fun y0 : real => exists y1 : real, (~ (real_lt y0 y1)) /\ ((real_le y0 y1) /\ (~ (y0 = y1)))) x0).
Definition term35 (x0 : real) (x1 : real) := (real_le x1 x0) /\ (real_le x0 x1).
Definition term250 (x0 : real) (x1 : real) := (fun y0 : real => real_lt y0 x0) x1.
Definition term57 (x0 : real) (x1 : real) := ((real_lt x0 x1) /\ ((~ (real_le x0 x1)) \/ (x0 = x1))) \/ ((~ (real_lt x0 x1)) /\ ((real_le x0 x1) /\ (~ (x0 = x1)))).
Definition term49 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term14 := (((~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> ((~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term76 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term97 (x0 : real) := (exists y0 : real, (real_lt x0 y0) /\ ((~ (real_le x0 y0)) \/ (x0 = y0))) \/ (exists y0 : real, (~ (real_lt x0 y0)) /\ ((real_le x0 y0) /\ (~ (x0 = y0)))).
Definition term16 := ~ (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))).
Definition term10 := ~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))).
Definition term12 := ((~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term91 (x0 : real) := exists y0 : real, (real_lt x0 y0) /\ ((~ (real_le x0 y0)) \/ (x0 = y0)).
Definition term144 (x0 : real) := fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0).
Definition term256 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term268 (x0 : real) (x1 : real) := (real_le x0 x1) -> ~ (real_le x0 x1).
Definition term116 := fun y0 : real => (fun y1 : real => exists y2 : real, (~ (real_lt y1 y2)) /\ ((real_le y1 y2) /\ (~ (y1 = y2)))) y0.
Definition term111 := fun y0 : real => (fun y1 : real => exists y2 : real, (real_lt y1 y2) /\ ((~ (real_le y1 y2)) \/ (y1 = y2))) y0.
Definition term77 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term289 (x0 : real) (x1 : real) := ((real_lt x1 x0) /\ (real_le x0 x1)) -> False.
Definition term305 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term216 (x0 : real) := (forall y0 : real, (real_lt y0 x0) \/ (real_le x0 y0)) /\ (forall y0 : real, (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))).
Definition term161 (x0 : real) := (forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) /\ (forall y0 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)).
Definition term241 (x0 : real) := forall y0 : real, ((real_le x0 y0) \/ (~ (x0 = y0))) /\ ((real_le y0 x0) \/ (~ (x0 = y0))).
Definition term194 (x0 : real) := forall y0 : real, ((real_lt y0 x0) \/ (real_le x0 y0)) /\ ((~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))).
Definition term300 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ ((x1 = x0) \/ (~ (real_le x0 x1))).
Definition term70 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) x0).
Definition term58 (x0 : real) (x1 : real) := ~ ((real_lt x0 x1) = ((real_le x0 x1) /\ (~ (x0 = x1)))).
Definition term103 := fun y0 : real => exists y1 : real, (~ (real_lt y0 y1)) /\ ((real_le y0 y1) /\ (~ (y0 = y1))).
Definition term102 := fun y0 : real => exists y1 : real, (real_lt y0 y1) /\ ((~ (real_le y0 y1)) \/ (y0 = y1)).
Definition term72 := fun y0 : real => exists y1 : real, ((real_lt y0 y1) /\ ((~ (real_le y0 y1)) \/ (y0 = y1))) \/ ((~ (real_lt y0 y1)) /\ ((real_le y0 y1) /\ (~ (y0 = y1)))).
Definition term13 := (((~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term143 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0)).
Definition term215 (x0 : real) := forall y0 : real, (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0)).
Definition term46 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) \/ (~ (~ (x0 = x1))).
Definition term213 (x0 : real) := fun y0 : real => (fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0.
Definition term153 (x0 : real) := fun y0 : real => (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0.
Definition term130 (x0 : real) (x1 : real) := and (((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1))).
Definition term148 (x0 : real) (x1 : real) := (fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)) x1.
Definition term110 := @eq Prop (exists y0 : real, (exists y1 : real, (real_lt y0 y1) /\ ((~ (real_le y0 y1)) \/ (y0 = y1))) \/ (exists y1 : real, (~ (real_lt y0 y1)) /\ ((real_le y0 y1) /\ (~ (y0 = y1))))).
Definition term109 := @eq Prop (exists y0 : real, ((fun y1 : real => exists y2 : real, (real_lt y1 y2) /\ ((~ (real_le y1 y2)) \/ (y1 = y2))) y0) \/ ((fun y1 : real => exists y2 : real, (~ (real_lt y1 y2)) /\ ((real_le y1 y2) /\ (~ (y1 = y2)))) y0)).
Definition term88 (x0 : real) := @eq Prop (exists y0 : real, ((real_lt x0 y0) /\ ((~ (real_le x0 y0)) \/ (x0 = y0))) \/ ((~ (real_lt x0 y0)) /\ ((real_le x0 y0) /\ (~ (x0 = y0))))).
Definition term87 (x0 : real) := @eq Prop (exists y0 : real, ((fun y1 : real => (real_lt x0 y1) /\ ((~ (real_le x0 y1)) \/ (x0 = y1))) y0) \/ ((fun y1 : real => (~ (real_lt x0 y1)) /\ ((real_le x0 y1) /\ (~ (x0 = y1)))) y0)).
Definition term221 := fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1).
Definition term167 := fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1).
Definition term38 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term33 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term253 (x0 : real) (x1 : real) := @eq Prop (real_lt x0 x1).
Definition term60 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term139 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term266 (x0 : real) (x1 : real) := imp (real_lt x0 x1).
Definition term290 (x0 : real) (x1 : real) := (real_lt x1 x0) /\ (real_le x0 x1).
Definition term246 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_le y0 y1) \/ (~ (y0 = y1))) /\ ((real_le y1 y0) \/ (~ (y0 = y1)))) x0.
Definition term244 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) x0.
Definition term225 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))) x0.
Definition term223 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) x0.
Definition term170 (x0 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)) x0.
Definition term168 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) x0.
Definition term69 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) x0.
Definition term127 (x0 : real) (x1 : real) := or ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1))).
Definition term9 := (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))))) -> False.
Definition term214 (x0 : real) := forall y0 : real, (fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0.
Definition term209 (x0 : real) := forall y0 : real, (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0.
Definition term159 (x0 : real) := forall y0 : real, (fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0.
Definition term154 (x0 : real) := forall y0 : real, (fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0.
Definition term31 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0).
Definition term11 := (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))))) -> (forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) -> False.
Definition term227 := fun y0 : real => ((fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0).
Definition term172 := fun y0 : real => ((fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0).
Definition term295 (x0 : real) (x1 : real) := @eq Prop ((real_lt x1 x0) \/ (real_le x0 x1)).
Definition term270 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_le x0 x1)).
Definition term262 (x0 : real) (x1 : real) := (~ (~ (real_lt x1 x0))) -> ~ (real_le x0 x1).
Definition term301 (x0 : real) (x1 : real) := (x1 = x0) \/ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1))).
Definition term189 (x0 : real) (x1 : real) := and ((real_lt x1 x0) \/ (~ (~ (real_le x0 x1)))).
Definition term36 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term248 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) \/ ((~ (real_le x1 x0)) \/ (x0 = x1)).
Definition term45 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term204 (x0 : real) (x1 : real) := ((fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0)) x1) /\ ((fun y0 : real => (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))) x1).
Definition term149 (x0 : real) (x1 : real) := ((fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) x1) /\ ((fun y0 : real => ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0)) x1).
Definition term309 (x0 : real) (x1 : real) := and (~ (~ (real_le x0 x1))).
Definition term299 (x0 : real) (x1 : real) := (x1 = x0) \/ (~ (real_le x0 x1)).
Definition term203 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0))) x1.
Definition term86 (x0 : real) := fun y0 : real => ((fun y1 : real => (real_lt x0 y1) /\ ((~ (real_le x0 y1)) \/ (x0 = y1))) y0) \/ ((fun y1 : real => (~ (real_lt x0 y1)) /\ ((real_le x0 y1) /\ (~ (x0 = y1)))) y0).
Definition term28 (x0 : real) := forall y0 : real, (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term240 (x0 : real) := fun y0 : real => ((real_le x0 y0) \/ (~ (x0 = y0))) /\ ((real_le y0 x0) \/ (~ (x0 = y0))).
Definition term100 := exists y0 : real, ((fun y1 : real => exists y2 : real, (real_lt y1 y2) /\ ((~ (real_le y1 y2)) \/ (y1 = y2))) y0) \/ ((fun y1 : real => exists y2 : real, (~ (real_lt y1 y2)) /\ ((real_le y1 y2) /\ (~ (y1 = y2)))) y0).
Definition term78 (x0 : real) := exists y0 : real, ((fun y1 : real => (real_lt x0 y1) /\ ((~ (real_le x0 y1)) \/ (x0 = y1))) y0) \/ ((fun y1 : real => (~ (real_lt x0 y1)) /\ ((real_le x0 y1) /\ (~ (x0 = y1)))) y0).
Definition term312 (x0 : real) (x1 : real) := imp ((real_le x1 x0) /\ (real_le x0 x1)).
Definition term264 (x0 : real) (x1 : real) := ~ (~ (real_lt x0 x1)).
Definition term96 (x0 : real) := exists y0 : real, (~ (real_lt x0 y0)) /\ ((real_le x0 y0) /\ (~ (x0 = y0))).
Definition term199 (x0 : real) := fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0).
Definition term247 (x0 : real) (x1 : real) := (fun y0 : real => ((real_le x0 y0) \/ (~ (x0 = y0))) /\ ((real_le y0 x0) \/ (~ (x0 = y0)))) x1.
Definition term26 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term83 (x0 : real) (x1 : real) := or ((fun y0 : real => (real_lt x0 y0) /\ ((~ (real_le x0 y0)) \/ (x0 = y0))) x1).
Definition term258 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) \/ (~ (real_lt x0 x1)).
Definition term218 := forall y0 : real, (forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) /\ (forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))).
Definition term163 := forall y0 : real, (forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)).
Definition term292 (x0 : real) := ((real_lt x0 x0) /\ (real_le x0 x0)) -> False.
Definition term307 (x0 : real) (x1 : real) := ~ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x1))).
Definition term41 (x0 : real) := fun y0 : real => (real_lt x0 y0) = ((real_le x0 y0) /\ (~ (x0 = y0))).
Definition term291 (x0 : real) := (real_lt x0 x0) /\ (real_le x0 x0).
Definition term94 (x0 : real) := fun y0 : real => (fun y1 : real => (~ (real_lt x0 y1)) /\ ((real_le x0 y1) /\ (~ (x0 = y1)))) y0.
Definition term89 (x0 : real) := fun y0 : real => (fun y1 : real => (real_lt x0 y1) /\ ((~ (real_le x0 y1)) \/ (x0 = y1))) y0.
Definition term236 := forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0.
Definition term231 := forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0.
Definition term181 := forall y0 : real, (fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0.
Definition term176 := forall y0 : real, (fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0.
Definition term27 (x0 : real) := fun y0 : real => (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term85 (x0 : real) (x1 : real) := ((fun y0 : real => (real_lt x0 y0) /\ ((~ (real_le x0 y0)) \/ (x0 = y0))) x1) \/ ((fun y0 : real => (~ (real_lt x0 y0)) /\ ((real_le x0 y0) /\ (~ (x0 = y0)))) x1).
Definition term188 (x0 : real) (x1 : real) := (real_lt x1 x0) \/ (real_le x0 x1).
Definition term226 (x0 : real) := ((fun y0 : real => forall y1 : real, (real_lt y1 y0) \/ (real_le y0 y1)) x0) /\ ((fun y0 : real => forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1))) x0).
Definition term171 (x0 : real) := ((fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1))) x0) /\ ((fun y0 : real => forall y1 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y0))) \/ (y0 = y1)) x0).
Definition term20 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> ~ (forall y0 : real, forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))).
Definition term310 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term278 (x0 : real) := ~ (x0 = x0).
Definition term205 (x0 : real) := fun y0 : real => ((fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ ((fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0).
Definition term150 (x0 : real) := fun y0 : real => ((fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0).
Definition term208 (x0 : real) := fun y0 : real => (fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0.
Definition term158 (x0 : real) := fun y0 : real => (fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term65 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_lt x0 y1) = ((real_le x0 y1) /\ (~ (x0 = y1)))) y0).
Definition term145 (x0 : real) (x1 : real) := (fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) x1.
Definition term67 (x0 : real) := exists y0 : real, ((real_lt x0 y0) /\ ((~ (real_le x0 y0)) \/ (x0 = y0))) \/ ((~ (real_lt x0 y0)) /\ ((real_le x0 y0) /\ (~ (x0 = y0)))).
Definition term239 (x0 : real) (x1 : real) := ((real_le x0 x1) \/ (~ (x0 = x1))) /\ ((real_le x1 x0) \/ (~ (x0 = x1))).
Definition term140 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term302 (x0 : real) (x1 : real) := @eq Prop ((~ (real_le x0 x1)) \/ ((~ (real_le x1 x0)) \/ (x0 = x1))).
Definition term283 (x0 : real) := (x0 = x0) -> real_le x0 x0.
Definition term137 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term200 (x0 : real) := fun y0 : real => (~ (real_lt y0 x0)) \/ (~ (real_le x0 y0)).
Definition term282 (x0 : real) (x1 : real) := (x1 = x0) -> real_le x0 x1.
Definition term84 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_lt x0 y0)) /\ ((real_le x0 y0) /\ (~ (x0 = y0)))) x1.
Definition term252 (x0 : real) (x1 : real) := @eq Prop ((fun y0 : real => real_lt y0 x0) x1).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term275 (x0 : real) := (~ (real_lt x0 x0)) -> real_lt x0 x0.
Definition term52 (x0 : real) (x1 : real) := (real_lt x0 x1) /\ (~ ((real_le x0 x1) /\ (~ (x0 = x1)))).
Definition term44 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term202 (x0 : real) (x1 : real) := and ((fun y0 : real => (real_lt y0 x0) \/ (real_le x0 y0)) x1).
Definition term147 (x0 : real) (x1 : real) := and ((fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0))) x1).
Definition term99 := exists y0 : real, (exists y1 : real, (real_lt y0 y1) /\ ((~ (real_le y0 y1)) \/ (y0 = y1))) \/ (exists y1 : real, (~ (real_lt y0 y1)) /\ ((real_le y0 y1) /\ (~ (y0 = y1)))).
Definition term108 := fun y0 : real => ((fun y1 : real => exists y2 : real, (real_lt y1 y2) /\ ((~ (real_le y1 y2)) \/ (y1 = y2))) y0) \/ ((fun y1 : real => exists y2 : real, (~ (real_lt y1 y2)) /\ ((real_le y1 y2) /\ (~ (y1 = y2)))) y0).
Definition term273 (x0 : real) (x1 : real) := (real_le x0 x1) -> False.
Definition term93 (x0 : real) := or (exists y0 : real, (real_lt x0 y0) /\ ((~ (real_le x0 y0)) \/ (x0 = y0))).
Definition term115 := or (exists y0 : real, exists y1 : real, (real_lt y0 y1) /\ ((~ (real_le y0 y1)) \/ (y0 = y1))).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term281 (x0 : real) (x1 : real) := imp (x0 = x1).
Definition term98 := fun y0 : real => (exists y1 : real, (real_lt y0 y1) /\ ((~ (real_le y0 y1)) \/ (y0 = y1))) \/ (exists y1 : real, (~ (real_lt y0 y1)) /\ ((real_le y0 y1) /\ (~ (y0 = y1)))).
Definition term308 (x0 : real) (x1 : real) := (~ (~ (real_le x1 x0))) /\ (~ (~ (real_le x0 x1))).
Definition term155 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) \/ (~ (x0 = y0)).
Definition term219 := forall y0 : real, ((fun y1 : real => forall y2 : real, (real_lt y2 y1) \/ (real_le y1 y2)) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_lt y2 y1)) \/ (~ (real_le y1 y2))) y0).
Definition term197 (x0 : real) := forall y0 : real, ((fun y1 : real => (real_lt y1 x0) \/ (real_le x0 y1)) y0) /\ ((fun y1 : real => (~ (real_lt y1 x0)) \/ (~ (real_le x0 y1))) y0).
Definition term164 := forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_le y1 y2) /\ (real_le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y1))) \/ (y1 = y2)) y0).
Definition term141 (x0 : real) := forall y0 : real, ((fun y1 : real => ((real_le x0 y1) /\ (real_le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => ((~ (real_le x0 y1)) \/ (~ (real_le y1 x0))) \/ (x0 = y1)) y0).
Definition term297 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) -> real_le x0 x1.
Definition term271 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) -> real_le x0 x1.
Definition term101 := (exists y0 : real, (fun y1 : real => exists y2 : real, (real_lt y1 y2) /\ ((~ (real_le y1 y2)) \/ (y1 = y2))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (~ (real_lt y1 y2)) /\ ((real_le y1 y2) /\ (~ (y1 = y2)))) y0).
Definition term79 (x0 : real) := (exists y0 : real, (fun y1 : real => (real_lt x0 y1) /\ ((~ (real_le x0 y1)) \/ (x0 = y1))) y0) \/ (exists y0 : real, (fun y1 : real => (~ (real_lt x0 y1)) /\ ((real_le x0 y1) /\ (~ (x0 = y1)))) y0).
Definition term245 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0)) x1.
Definition term24 := imp (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))))).
Definition term269 (x0 : Prop) := x0 -> ~ x0.
Definition term222 := fun y0 : real => forall y1 : real, (~ (real_lt y1 y0)) \/ (~ (real_le y0 y1)).
Definition term166 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) \/ (~ (y0 = y1)).
Definition term29 := fun y0 : real => forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1)).
Definition term192 (x0 : real) (x1 : real) := ((real_lt x1 x0) \/ (real_le x0 x1)) /\ ((~ (real_lt x1 x0)) \/ (~ (real_le x0 x1))).
Definition term146 (x0 : real) (x1 : real) := ((real_le x0 x1) /\ (real_le x1 x0)) \/ (~ (x0 = x1)).
Definition term160 (x0 : real) := forall y0 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 x0))) \/ (x0 = y0).
Definition term42 (x0 : real) := forall y0 : real, (real_lt x0 y0) = ((real_le x0 y0) /\ (~ (x0 = y0))).
Definition term280 (x0 : real) (x1 : real) := imp (~ (~ (x0 = x1))).
Definition term265 (x0 : real) (x1 : real) := imp (~ (~ (real_lt x0 x1))).
Definition term117 := exists y0 : real, (fun y1 : real => exists y2 : real, (~ (real_lt y1 y2)) /\ ((real_le y1 y2) /\ (~ (y1 = y2)))) y0.
Definition term112 := exists y0 : real, (fun y1 : real => exists y2 : real, (real_lt y1 y2) /\ ((~ (real_le y1 y2)) \/ (y1 = y2))) y0.
Definition term123 (x0 : real) := @eq Prop ((exists y0 : real, (real_lt x0 y0) /\ ((~ (real_le x0 y0)) \/ (x0 = y0))) \/ (exists y0 : real, (~ (real_lt x0 y0)) /\ ((real_le x0 y0) /\ (~ (x0 = y0))))).
Definition term122 (x0 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => (real_lt x0 y1) /\ ((~ (real_le x0 y1)) \/ (x0 = y1))) y0) \/ (exists y0 : real, (fun y1 : real => (~ (real_lt x0 y1)) /\ ((real_le x0 y1) /\ (~ (x0 = y1)))) y0)).
Definition term121 := @eq Prop ((exists y0 : real, exists y1 : real, (real_lt y0 y1) /\ ((~ (real_le y0 y1)) \/ (y0 = y1))) \/ (exists y0 : real, exists y1 : real, (~ (real_lt y0 y1)) /\ ((real_le y0 y1) /\ (~ (y0 = y1))))).
Definition term120 := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, (real_lt y1 y2) /\ ((~ (real_le y1 y2)) \/ (y1 = y2))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (~ (real_lt y1 y2)) /\ ((real_le y1 y2) /\ (~ (y1 = y2)))) y0)).
