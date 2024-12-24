Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term148 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) \/ (real_le x0 x1).
Definition term89 (x0 : real) (x1 : real) := and ((real_lt x0 x1) \/ ((~ (real_le x0 x1)) \/ (x0 = x1))).
Definition term35 (x0 : real -> Prop) := ~ (all x0).
Definition term226 := (~ False) -> False.
Definition term225 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) (sqrt x0)) -> False.
Definition term198 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term99 (x0 : real) := fun y0 : real => (~ (real_lt x0 y0)) \/ ((real_le x0 y0) /\ (~ (x0 = y0))).
Definition term81 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) \/ (x0 = x1).
Definition term159 (x0 : Prop) := ~ (~ x0).
Definition term52 := fun y0 : real => ((sqrt y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0)))).
Definition term26 := real_of_num (NUMERAL 0).
Definition term98 (x0 : real) := fun y0 : real => (real_lt x0 y0) \/ ((~ (real_le x0 y0)) \/ (x0 = y0)).
Definition term151 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> real_lt (real_of_num (NUMERAL 0)) x0.
Definition term18 := (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> ~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))).
Definition term133 := and (forall y0 : real, forall y1 : real, (real_lt y0 y1) \/ ((~ (real_le y0 y1)) \/ (y0 = y1))).
Definition term54 (x0 : real) := (fun y0 : real => ((sqrt y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))) x0.
Definition term92 (x0 : real) := fun y0 : real => ((real_lt x0 y0) \/ ((~ (real_le x0 y0)) \/ (x0 = y0))) /\ ((~ (real_lt x0 y0)) \/ ((real_le x0 y0) /\ (~ (x0 = y0)))).
Definition term147 (x0 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) (sqrt x0)).
Definition term111 (x0 : real) := and (forall y0 : real, (real_lt x0 y0) \/ ((~ (real_le x0 y0)) \/ (x0 = y0))).
Definition term68 := and (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))).
Definition term205 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> ~ ((sqrt x0) = (real_of_num (NUMERAL 0))).
Definition term180 (x0 : real) (x1 : real) := (~ (x0 = x1)) \/ (~ (real_lt x0 x1)).
Definition term216 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term123 (x0 : real) := and ((fun y0 : real => forall y1 : real, (real_lt y0 y1) \/ ((~ (real_le y0 y1)) \/ (y0 = y1))) x0).
Definition term42 := exists y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) /\ (~ (real_lt (real_of_num (NUMERAL 0)) (sqrt y0))).
Definition term173 (x0 : real) := imp (real_le (real_of_num (NUMERAL 0)) x0).
Definition term76 := fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt y0)).
Definition term12 := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) -> False.
Definition term132 := and (forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ ((~ (real_le y1 y2)) \/ (y1 = y2))) y0).
Definition term110 (x0 : real) := and (forall y0 : real, (fun y1 : real => (real_lt x0 y1) \/ ((~ (real_le x0 y1)) \/ (x0 = y1))) y0).
Definition term67 := and (forall y0 : real, (fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL 0))) \/ (~ (y1 = (real_of_num (NUMERAL 0))))) y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term3 := ~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0)).
Definition term43 (x0 : real) := (((sqrt x0) = (real_of_num (NUMERAL 0))) \/ (~ (x0 = (real_of_num (NUMERAL 0))))) /\ ((~ ((sqrt x0) = (real_of_num (NUMERAL 0)))) \/ (x0 = (real_of_num (NUMERAL 0)))).
Definition term116 := fun y0 : real => (forall y1 : real, (real_lt y0 y1) \/ ((~ (real_le y0 y1)) \/ (y0 = y1))) /\ (forall y1 : real, (~ (real_lt y0 y1)) \/ ((real_le y0 y1) /\ (~ (y0 = y1)))).
Definition term90 (x0 : real) (x1 : real) := ((real_lt x0 x1) \/ (~ ((real_le x0 x1) /\ (~ (x0 = x1))))) /\ ((~ (real_lt x0 x1)) \/ ((real_le x0 x1) /\ (~ (x0 = x1)))).
Definition term211 (x0 : real) := ((real_of_num (NUMERAL 0)) = (sqrt x0)) -> ~ ((real_of_num (NUMERAL 0)) = (sqrt x0)).
Definition term23 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term137 := (forall y0 : real, forall y1 : real, (real_lt y0 y1) \/ ((~ (real_le y0 y1)) \/ (y0 = y1))) /\ (forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) \/ ((real_le y0 y1) /\ (~ (y0 = y1)))).
Definition term24 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0).
Definition term85 (x0 : real) (x1 : real) := or (real_lt x0 x1).
Definition term157 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term184 (x0 : real) (x1 : real) := (real_lt x0 x1) -> ~ (x0 = x1).
Definition term119 := (forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ ((~ (real_le y1 y2)) \/ (y1 = y2))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ ((real_le y1 y2) /\ (~ (y1 = y2)))) y0).
Definition term97 (x0 : real) := (forall y0 : real, (fun y1 : real => (real_lt x0 y1) \/ ((~ (real_le x0 y1)) \/ (x0 = y1))) y0) /\ (forall y0 : real, (fun y1 : real => (~ (real_lt x0 y1)) \/ ((real_le x0 y1) /\ (~ (x0 = y1)))) y0).
Definition term51 := (forall y0 : real, (fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL 0))) \/ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) /\ (forall y0 : real, (fun y1 : real => (~ ((sqrt y1) = (real_of_num (NUMERAL 0)))) \/ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term149 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) \/ (~ (x0 = x1)).
Definition term178 (x0 : real) := (~ (x0 = x0)) -> x0 = x0.
Definition term146 (x0 : real) (x1 : real) := (fun y0 : real => ((~ (real_lt x0 y0)) \/ (real_le x0 y0)) /\ ((~ (real_lt x0 y0)) \/ (~ (x0 = y0)))) x1.
Definition term19 (x0 : real) (x1 : real) := (real_le x0 x1) /\ (~ (x0 = x1)).
Definition term153 (x0 : Prop) := (~ x0) -> x0.
Definition term156 (x0 : real) (x1 : real) := @eq Prop ((real_le x0 x1) \/ (~ (real_lt x0 x1))).
Definition term189 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x1 = x0)) \/ (x2 = x0))) -> ~ (x1 = x2).
Definition term182 (x0 : real) (x1 : real) := @eq Prop ((~ (x0 = x1)) \/ (~ (real_lt x0 x1))).
Definition term181 (x0 : real) (x1 : real) := @eq Prop ((~ (real_lt x0 x1)) \/ (~ (x0 = x1))).
Definition term134 := fun y0 : real => (fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ ((real_le y1 y2) /\ (~ (y1 = y2)))) y0.
Definition term129 := fun y0 : real => (fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ ((~ (real_le y1 y2)) \/ (y1 = y2))) y0.
Definition term102 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_lt x0 y0)) \/ ((real_le x0 y0) /\ (~ (x0 = y0)))) x1.
Definition term192 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term166 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term204 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term158 (x0 : real) (x1 : real) := (~ (~ (real_lt x0 x1))) -> real_le x0 x1.
Definition term143 := forall y0 : real, forall y1 : real, ((~ (real_lt y0 y1)) \/ (real_le y0 y1)) /\ ((~ (real_lt y0 y1)) \/ (~ (y0 = y1))).
Definition term136 := forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) \/ ((real_le y0 y1) /\ (~ (y0 = y1))).
Definition term131 := forall y0 : real, forall y1 : real, (real_lt y0 y1) \/ ((~ (real_le y0 y1)) \/ (y0 = y1)).
Definition term95 := forall y0 : real, forall y1 : real, ((real_lt y0 y1) \/ ((~ (real_le y0 y1)) \/ (y0 = y1))) /\ ((~ (real_lt y0 y1)) \/ ((real_le y0 y1) /\ (~ (y0 = y1)))).
Definition term10 := forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))).
Definition term200 (x0 : real) (x1 : real) (x2 : real) := ((x1 = x0) /\ (~ (x2 = x0))) -> ~ (x1 = x2).
Definition term155 (x0 : real) (x1 : real) := @eq Prop ((~ (real_lt x0 x1)) \/ (real_le x0 x1)).
Definition term163 (x0 : real) (x1 : real) := (real_lt x0 x1) -> real_le x0 x1.
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term41 := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) /\ (~ (real_lt (real_of_num (NUMERAL 0)) (sqrt y0))).
Definition term221 (x0 : real) (x1 : real) := ((real_le x0 x1) /\ (~ (x0 = x1))) -> real_lt x0 x1.
Definition term170 (x0 : real) := (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))) -> real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term152 (x0 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term165 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term86 (x0 : real) (x1 : real) := (real_lt x0 x1) \/ (~ ((real_le x0 x1) /\ (~ (x0 = x1)))).
Definition term82 (x0 : real) (x1 : real) := ~ ((real_le x0 x1) /\ (~ (x0 = x1))).
Definition term203 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term37 := exists y0 : real, ~ ((fun y1 : real => (real_lt (real_of_num (NUMERAL 0)) y1) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y1)) y0).
Definition term73 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt x0)).
Definition term112 (x0 : real) := fun y0 : real => (fun y1 : real => (~ (real_lt x0 y1)) \/ ((real_le x0 y1) /\ (~ (x0 = y1)))) y0.
Definition term107 (x0 : real) := fun y0 : real => (fun y1 : real => (real_lt x0 y1) \/ ((~ (real_le x0 y1)) \/ (x0 = y1))) y0.
Definition term69 := fun y0 : real => (fun y1 : real => (~ ((sqrt y1) = (real_of_num (NUMERAL 0)))) \/ (y1 = (real_of_num (NUMERAL 0)))) y0.
Definition term209 (x0 : real) := (((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))) /\ (~ ((sqrt x0) = (real_of_num (NUMERAL 0))))) -> ~ ((real_of_num (NUMERAL 0)) = (sqrt x0)).
Definition term77 := forall y0 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt y0)).
Definition term167 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) (sqrt x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term128 := @eq Prop (forall y0 : real, (forall y1 : real, (real_lt y0 y1) \/ ((~ (real_le y0 y1)) \/ (y0 = y1))) /\ (forall y1 : real, (~ (real_lt y0 y1)) \/ ((real_le y0 y1) /\ (~ (y0 = y1))))).
Definition term127 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ ((~ (real_le y1 y2)) \/ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ ((real_le y1 y2) /\ (~ (y1 = y2)))) y0)).
Definition term106 (x0 : real) := @eq Prop (forall y0 : real, ((real_lt x0 y0) \/ ((~ (real_le x0 y0)) \/ (x0 = y0))) /\ ((~ (real_lt x0 y0)) \/ ((real_le x0 y0) /\ (~ (x0 = y0))))).
Definition term105 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (real_lt x0 y1) \/ ((~ (real_le x0 y1)) \/ (x0 = y1))) y0) /\ ((fun y1 : real => (~ (real_lt x0 y1)) \/ ((real_le x0 y1) /\ (~ (x0 = y1)))) y0)).
Definition term63 := @eq Prop (forall y0 : real, (((sqrt y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))) /\ ((~ ((sqrt y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0))))).
Definition term62 := @eq Prop (forall y0 : real, ((fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL 0))) \/ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) /\ ((fun y1 : real => (~ ((sqrt y1) = (real_of_num (NUMERAL 0)))) \/ (y1 = (real_of_num (NUMERAL 0)))) y0)).
Definition term150 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term174 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) (sqrt x0))) -> real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term142 := fun y0 : real => forall y1 : real, ((~ (real_lt y0 y1)) \/ (real_le y0 y1)) /\ ((~ (real_lt y0 y1)) \/ (~ (y0 = y1))).
Definition term121 := fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ ((real_le y0 y1) /\ (~ (y0 = y1))).
Definition term120 := fun y0 : real => forall y1 : real, (real_lt y0 y1) \/ ((~ (real_le y0 y1)) \/ (y0 = y1)).
Definition term94 := fun y0 : real => forall y1 : real, ((real_lt y0 y1) \/ ((~ (real_le y0 y1)) \/ (y0 = y1))) /\ ((~ (real_lt y0 y1)) \/ ((real_le y0 y1) /\ (~ (y0 = y1)))).
Definition term22 := fun y0 : real => forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1))).
Definition term8 := (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) -> False.
Definition term219 (x0 : real) (x1 : real) := imp (~ ((~ (real_le x0 x1)) \/ (x0 = x1))).
Definition term83 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term7 := (((~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) -> False) -> (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) -> False) -> ((~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) -> False) -> (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) -> False.
Definition term9 := ~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))).
Definition term71 := forall y0 : real, (~ ((sqrt y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0))).
Definition term87 (x0 : real) (x1 : real) := (real_lt x0 x1) \/ ((~ (real_le x0 x1)) \/ (x0 = x1)).
Definition term5 := ((~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) -> False) -> (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) -> False.
Definition term75 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term139 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term223 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) (sqrt x0)) /\ (~ ((real_of_num (NUMERAL 0)) = (sqrt x0)))) -> real_lt (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term175 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) (sqrt x0)).
Definition term222 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) (sqrt x0)) /\ (~ ((real_of_num (NUMERAL 0)) = (sqrt x0))).
Definition term201 (x0 : real) := (x0 = x0) /\ (~ ((real_of_num (NUMERAL 0)) = x0)).
Definition term30 := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0).
Definition term13 := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> ~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))).
Definition term57 (x0 : real) := and (((sqrt x0) = (real_of_num (NUMERAL 0))) \/ (~ (x0 = (real_of_num (NUMERAL 0))))).
Definition term56 (x0 : real) := and ((fun y0 : real => ((sqrt y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))) x0).
Definition term212 (x0 : real) (x1 : real) := (~ ((~ (real_le x0 x1)) \/ (x0 = x1))) -> real_lt x0 x1.
Definition term191 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term115 (x0 : real) := (forall y0 : real, (real_lt x0 y0) \/ ((~ (real_le x0 y0)) \/ (x0 = y0))) /\ (forall y0 : real, (~ (real_lt x0 y0)) \/ ((real_le x0 y0) /\ (~ (x0 = y0)))).
Definition term72 := (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))) /\ (forall y0 : real, (~ ((sqrt y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term141 (x0 : real) := forall y0 : real, ((~ (real_lt x0 y0)) \/ (real_le x0 y0)) /\ ((~ (real_lt x0 y0)) \/ (~ (x0 = y0))).
Definition term176 := (~ ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0)))) -> (real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0)).
Definition term55 (x0 : real) := ((sqrt x0) = (real_of_num (NUMERAL 0))) \/ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term53 := fun y0 : real => (~ ((sqrt y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0))).
Definition term197 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) /\ (~ (x1 = x2)).
Definition term6 := (((~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) -> False) -> (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) -> False) -> (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) -> False.
Definition term60 (x0 : real) := ((fun y0 : real => ((sqrt y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))) x0) /\ ((fun y0 : real => (~ ((sqrt y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0)))) x0).
Definition term80 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) \/ (~ (~ (x0 = x1))).
Definition term27 := fun y0 : real => ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term138 (x0 : real) (x1 : real) := ((~ (real_lt x0 x1)) \/ (real_le x0 x1)) /\ ((~ (real_lt x0 x1)) \/ (~ (x0 = x1))).
Definition term64 := fun y0 : real => (fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL 0))) \/ (~ (y1 = (real_of_num (NUMERAL 0))))) y0.
Definition term169 (x0 : real) := @eq Prop ((real_le (real_of_num (NUMERAL 0)) (sqrt x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term91 (x0 : real) (x1 : real) := ((real_lt x0 x1) \/ ((~ (real_le x0 x1)) \/ (x0 = x1))) /\ ((~ (real_lt x0 x1)) \/ ((real_le x0 x1) /\ (~ (x0 = x1)))).
Definition term36 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term48 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term202 (x0 : real) := ((x0 = x0) /\ (~ ((real_of_num (NUMERAL 0)) = x0))) -> ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term162 (x0 : real) (x1 : real) := imp (real_lt x0 x1).
Definition term145 (x0 : real) := (fun y0 : real => forall y1 : real, ((~ (real_lt y0 y1)) \/ (real_le y0 y1)) /\ ((~ (real_lt y0 y1)) \/ (~ (y0 = y1)))) x0.
Definition term124 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ ((real_le y0 y1) /\ (~ (y0 = y1)))) x0.
Definition term122 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y0 y1) \/ ((~ (real_le y0 y1)) \/ (y0 = y1))) x0.
Definition term144 (x0 : real) := (fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt y0))) x0.
Definition term74 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term2 := (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0))) -> False.
Definition term113 (x0 : real) := forall y0 : real, (fun y1 : real => (~ (real_lt x0 y1)) \/ ((real_le x0 y1) /\ (~ (x0 = y1)))) y0.
Definition term108 (x0 : real) := forall y0 : real, (fun y1 : real => (real_lt x0 y1) \/ ((~ (real_le x0 y1)) \/ (x0 = y1))) y0.
Definition term70 := forall y0 : real, (fun y1 : real => (~ ((sqrt y1) = (real_of_num (NUMERAL 0)))) \/ (y1 = (real_of_num (NUMERAL 0)))) y0.
Definition term65 := forall y0 : real, (fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL 0))) \/ (~ (y1 = (real_of_num (NUMERAL 0))))) y0.
Definition term100 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt x0 y0) \/ ((~ (real_le x0 y0)) \/ (x0 = y0))) x1.
Definition term88 (x0 : real) (x1 : real) := and ((real_lt x0 x1) \/ (~ ((real_le x0 x1) /\ (~ (x0 = x1))))).
Definition term4 := (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0))) -> (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) -> False.
Definition term140 (x0 : real) := fun y0 : real => ((~ (real_lt x0 y0)) \/ (real_le x0 y0)) /\ ((~ (real_lt x0 y0)) \/ (~ (x0 = y0))).
Definition term224 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) (sqrt x0))) -> real_lt (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term126 := fun y0 : real => ((fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ ((~ (real_le y1 y2)) \/ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ ((real_le y1 y2) /\ (~ (y1 = y2)))) y0).
Definition term220 (x0 : real) (x1 : real) := imp ((real_le x0 x1) /\ (~ (x0 = x1))).
Definition term79 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term103 (x0 : real) (x1 : real) := ((fun y0 : real => (real_lt x0 y0) \/ ((~ (real_le x0 y0)) \/ (x0 = y0))) x1) /\ ((fun y0 : real => (~ (real_lt x0 y0)) \/ ((real_le x0 y0) /\ (~ (x0 = y0)))) x1).
Definition term109 (x0 : real) := forall y0 : real, (real_lt x0 y0) \/ ((~ (real_le x0 y0)) \/ (x0 = y0)).
Definition term217 (x0 : real) (x1 : real) := and (~ (~ (real_le x0 x1))).
Definition term195 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term38 (x0 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0)) x0.
Definition term194 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x0 = x2))) /\ (~ (x1 = x2)).
Definition term33 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term16 := (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> ~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))).
Definition term160 (x0 : real) (x1 : real) := ~ (~ (real_lt x0 x1)).
Definition term25 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0).
Definition term1 := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0).
Definition term215 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term59 (x0 : real) := (~ ((sqrt x0) = (real_of_num (NUMERAL 0)))) \/ (x0 = (real_of_num (NUMERAL 0))).
Definition term114 (x0 : real) := forall y0 : real, (~ (real_lt x0 y0)) \/ ((real_le x0 y0) /\ (~ (x0 = y0))).
Definition term117 := forall y0 : real, (forall y1 : real, (real_lt y0 y1) \/ ((~ (real_le y0 y1)) \/ (y0 = y1))) /\ (forall y1 : real, (~ (real_lt y0 y1)) \/ ((real_le y0 y1) /\ (~ (y0 = y1)))).
Definition term154 (x0 : real) (x1 : real) := (real_le x0 x1) \/ (~ (real_lt x0 x1)).
Definition term213 (x0 : real) (x1 : real) := ~ ((~ (real_le x0 x1)) \/ (x0 = x1)).
Definition term186 (x0 : real) := ~ ((real_of_num (NUMERAL 0)) = x0).
Definition term66 := forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0)))).
Definition term20 (x0 : real) := fun y0 : real => (real_lt x0 y0) = ((real_le x0 y0) /\ (~ (x0 = y0))).
Definition term58 (x0 : real) := (fun y0 : real => (~ ((sqrt y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0)))) x0.
Definition term135 := forall y0 : real, (fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ ((real_le y1 y2) /\ (~ (y1 = y2)))) y0.
Definition term130 := forall y0 : real, (fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ ((~ (real_le y1 y2)) \/ (y1 = y2))) y0.
Definition term28 := forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term196 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term125 (x0 : real) := ((fun y0 : real => forall y1 : real, (real_lt y0 y1) \/ ((~ (real_le y0 y1)) \/ (y0 = y1))) x0) /\ ((fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ ((real_le y0 y1) /\ (~ (y0 = y1)))) x0).
Definition term29 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term218 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term179 (x0 : real) := ~ (x0 = x0).
Definition term183 (x0 : real) (x1 : real) := (~ (~ (real_lt x0 x1))) -> ~ (x0 = x1).
Definition term104 (x0 : real) := fun y0 : real => ((fun y1 : real => (real_lt x0 y1) \/ ((~ (real_le x0 y1)) \/ (x0 = y1))) y0) /\ ((fun y1 : real => (~ (real_lt x0 y1)) \/ ((real_le x0 y1) /\ (~ (x0 = y1)))) y0).
Definition term61 := fun y0 : real => ((fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL 0))) \/ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) /\ ((fun y1 : real => (~ ((sqrt y1) = (real_of_num (NUMERAL 0)))) \/ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term93 (x0 : real) := forall y0 : real, ((real_lt x0 y0) \/ ((~ (real_le x0 y0)) \/ (x0 = y0))) /\ ((~ (real_lt x0 y0)) \/ ((real_le x0 y0) /\ (~ (x0 = y0)))).
Definition term45 := forall y0 : real, (((sqrt y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))) /\ ((~ ((sqrt y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term168 (x0 : real) := @eq Prop ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt x0))).
Definition term14 := imp (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))).
Definition term11 := imp (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)).
Definition term39 (x0 : real) := ~ ((fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0)) x0).
Definition term40 := fun y0 : real => ~ ((fun y1 : real => (real_lt (real_of_num (NUMERAL 0)) y1) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y1)) y0).
Definition term49 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term185 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> ~ ((real_of_num (NUMERAL 0)) = x0).
Definition term32 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (~ (real_lt (real_of_num (NUMERAL 0)) (sqrt x0))).
Definition term206 (x0 : real) := ~ ((sqrt x0) = (real_of_num (NUMERAL 0))).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term44 := fun y0 : real => (((sqrt y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))) /\ ((~ ((sqrt y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term31 (x0 : real) := ~ ((real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt x0)).
Definition term207 (x0 : real) := ((sqrt x0) = (real_of_num (NUMERAL 0))) -> ~ ((sqrt x0) = (real_of_num (NUMERAL 0))).
Definition term210 (x0 : real) := ~ ((real_of_num (NUMERAL 0)) = (sqrt x0)).
Definition term84 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) \/ ((real_le x0 x1) /\ (~ (x0 = x1))).
Definition term190 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term34 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term78 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term164 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term101 (x0 : real) (x1 : real) := and ((fun y0 : real => (real_lt x0 y0) \/ ((~ (real_le x0 y0)) \/ (x0 = y0))) x1).
Definition term171 (x0 : real) := ~ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term15 := (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) = ((real_le y0 y1) /\ (~ (y0 = y1)))) -> False.
Definition term118 := forall y0 : real, ((fun y1 : real => forall y2 : real, (real_lt y1 y2) \/ ((~ (real_le y1 y2)) \/ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, (~ (real_lt y1 y2)) \/ ((real_le y1 y2) /\ (~ (y1 = y2)))) y0).
Definition term96 (x0 : real) := forall y0 : real, ((fun y1 : real => (real_lt x0 y1) \/ ((~ (real_le x0 y1)) \/ (x0 = y1))) y0) /\ ((fun y1 : real => (~ (real_lt x0 y1)) \/ ((real_le x0 y1) /\ (~ (x0 = y1)))) y0).
Definition term50 := forall y0 : real, ((fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL 0))) \/ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) /\ ((fun y1 : real => (~ ((sqrt y1) = (real_of_num (NUMERAL 0)))) \/ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term193 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term187 (x0 : real) := ((real_of_num (NUMERAL 0)) = x0) -> ~ ((real_of_num (NUMERAL 0)) = x0).
Definition term17 := imp (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (sqrt y0))).
Definition term172 (x0 : real) := imp (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term188 (x0 : Prop) := x0 -> ~ x0.
Definition term208 (x0 : real) := ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))) /\ (~ ((sqrt x0) = (real_of_num (NUMERAL 0)))).
Definition term177 := ~ ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))).
Definition term199 (x0 : real) (x1 : real) (x2 : real) := imp ((x0 = x2) /\ (~ (x1 = x2))).
Definition term214 (x0 : real) (x1 : real) := (~ (~ (real_le x0 x1))) /\ (~ (x0 = x1)).
Definition term21 (x0 : real) := forall y0 : real, (real_lt x0 y0) = ((real_le x0 y0) /\ (~ (x0 = y0))).
Definition term161 (x0 : real) (x1 : real) := imp (~ (~ (real_lt x0 x1))).
