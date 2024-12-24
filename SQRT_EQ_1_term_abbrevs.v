Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 := imp ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term17 (x0 : real) := forall y0 : real, ((sqrt x0) = (sqrt y0)) = (x0 = y0).
Definition term169 := (~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))))) -> (sqrt (real_of_num (NUMERAL (BIT1 0)))) = (sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))).
Definition term165 := (~ ((sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))))) -> (sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))).
Definition term23 (x0 : real -> Prop) := ~ (all x0).
Definition term190 := (~ False) -> False.
Definition term78 (x0 : real) (x1 : real) := (fun y0 : real => (~ ((sqrt x0) = (sqrt y0))) \/ (x0 = y0)) x1.
Definition term49 := fun y0 : real => (fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0.
Definition term115 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL (BIT1 0)))).
Definition term144 (x0 : Prop) := ~ (~ x0).
Definition term42 (x0 : real) := or (((sqrt x0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (x0 = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term161 := ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (real_of_num (NUMERAL (BIT1 0)))).
Definition term15 := (~ (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ~ (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1)).
Definition term110 := and (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) \/ (~ (y0 = y1))).
Definition term178 (x0 : real) (x1 : real) := imp ((sqrt x0) = (sqrt x1)).
Definition term181 := (~ ((real_of_num (NUMERAL (BIT1 0))) = (sqrt (real_of_num (NUMERAL (BIT1 0)))))) -> (real_of_num (NUMERAL (BIT1 0))) = (sqrt (real_of_num (NUMERAL (BIT1 0)))).
Definition term88 (x0 : real) := and (forall y0 : real, ((sqrt x0) = (sqrt y0)) \/ (~ (x0 = y0))).
Definition term173 (x0 : real) (x1 : real) := @eq Prop ((~ ((sqrt x0) = (sqrt x1))) \/ (x0 = x1)).
Definition term143 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term100 (x0 : real) := and ((fun y0 : real => forall y1 : real, ((sqrt y0) = (sqrt y1)) \/ (~ (y0 = y1))) x0).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term121 (x0 : real) := @eq Prop ((fun y0 : real => ~ ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0))))) x0).
Definition term172 (x0 : real) (x1 : real) := ~ ((sqrt x0) = (sqrt x1)).
Definition term109 := and (forall y0 : real, (fun y1 : real => forall y2 : real, ((sqrt y1) = (sqrt y2)) \/ (~ (y1 = y2))) y0).
Definition term87 (x0 : real) := and (forall y0 : real, (fun y1 : real => ((sqrt x0) = (sqrt y1)) \/ (~ (x0 = y1))) y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term149 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term3 := ~ (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term119 := (fun y0 : real => ~ ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term93 := fun y0 : real => (forall y1 : real, ((sqrt y0) = (sqrt y1)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (~ ((sqrt y0) = (sqrt y1))) \/ (y0 = y1)).
Definition term183 (x0 : real) := ((real_of_num (NUMERAL (BIT1 0))) = (sqrt x0)) /\ ((real_of_num (NUMERAL (BIT1 0))) = (sqrt (real_of_num (NUMERAL (BIT1 0))))).
Definition term114 := (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) \/ (~ (y0 = y1))) /\ (forall y0 : real, forall y1 : real, (~ ((sqrt y0) = (sqrt y1))) \/ (y0 = y1)).
Definition term137 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term180 := ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (sqrt (sqrt (real_of_num (NUMERAL (BIT1 0)))))) -> (real_of_num (NUMERAL (BIT1 0))) = (sqrt (real_of_num (NUMERAL (BIT1 0)))).
Definition term96 := (forall y0 : real, (fun y1 : real => forall y2 : real, ((sqrt y1) = (sqrt y2)) \/ (~ (y1 = y2))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (~ ((sqrt y1) = (sqrt y2))) \/ (y1 = y2)) y0).
Definition term71 (x0 : real) := (forall y0 : real, (fun y1 : real => ((sqrt x0) = (sqrt y1)) \/ (~ (x0 = y1))) y0) /\ (forall y0 : real, (fun y1 : real => (~ ((sqrt x0) = (sqrt y1))) \/ (x0 = y1)) y0).
Definition term185 (x0 : real) := (~ ((sqrt x0) = (sqrt (real_of_num (NUMERAL (BIT1 0)))))) -> (sqrt x0) = (sqrt (real_of_num (NUMERAL (BIT1 0)))).
Definition term73 (x0 : real) := fun y0 : real => (~ ((sqrt x0) = (sqrt y0))) \/ (x0 = y0).
Definition term116 (x0 : real) := ~ ((sqrt x0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term163 := (~ ((sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (real_of_num (NUMERAL (BIT1 0)))))) -> (sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (real_of_num (NUMERAL (BIT1 0)))).
Definition term125 (x0 : Prop) := (~ x0) -> x0.
Definition term117 := fun y0 : real => ~ ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term139 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term111 := fun y0 : real => (fun y1 : real => forall y2 : real, (~ ((sqrt y1) = (sqrt y2))) \/ (y1 = y2)) y0.
Definition term106 := fun y0 : real => (fun y1 : real => forall y2 : real, ((sqrt y1) = (sqrt y2)) \/ (~ (y1 = y2))) y0.
Definition term141 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term135 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term61 (x0 : real) (x1 : real) := (((sqrt x0) = (sqrt x1)) \/ (~ (x0 = x1))) /\ ((~ ((sqrt x0) = (sqrt x1))) \/ (x0 = x1)).
Definition term182 := ~ ((real_of_num (NUMERAL (BIT1 0))) = (sqrt (real_of_num (NUMERAL (BIT1 0))))).
Definition term55 := exists y0 : real, (fun y1 : real => (~ ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0.
Definition term50 := exists y0 : real, (fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0.
Definition term113 := forall y0 : real, forall y1 : real, (~ ((sqrt y0) = (sqrt y1))) \/ (y0 = y1).
Definition term108 := forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) \/ (~ (y0 = y1)).
Definition term65 := forall y0 : real, forall y1 : real, (((sqrt y0) = (sqrt y1)) \/ (~ (y0 = y1))) /\ ((~ ((sqrt y0) = (sqrt y1))) \/ (y0 = y1)).
Definition term10 := forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1).
Definition term12 := ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1)) -> False.
Definition term13 := ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> ~ (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1)).
Definition term136 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term63 (x0 : real) := forall y0 : real, (((sqrt x0) = (sqrt y0)) \/ (~ (x0 = y0))) /\ ((~ ((sqrt x0) = (sqrt y0))) \/ (x0 = y0)).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term126 (x0 : real) := (~ ((sqrt x0) = (sqrt x0))) -> (sqrt x0) = (sqrt x0).
Definition term52 := or (exists y0 : real, (fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0).
Definition term171 (x0 : real) (x1 : real) := (x0 = x1) \/ (~ ((sqrt x0) = (sqrt x1))).
Definition term133 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term118 (x0 : real) := (fun y0 : real => ~ ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term25 := exists y0 : real, ~ ((fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0)))) = (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term4 := (~ (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1)) -> False.
Definition term152 (x0 : real) := ((sqrt x0) = (real_of_num (NUMERAL (BIT1 0)))) /\ ((sqrt x0) = (sqrt x0)).
Definition term105 := @eq Prop (forall y0 : real, (forall y1 : real, ((sqrt y0) = (sqrt y1)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (~ ((sqrt y0) = (sqrt y1))) \/ (y0 = y1))).
Definition term104 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, ((sqrt y1) = (sqrt y2)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, (~ ((sqrt y1) = (sqrt y2))) \/ (y1 = y2)) y0)).
Definition term83 (x0 : real) := @eq Prop (forall y0 : real, (((sqrt x0) = (sqrt y0)) \/ (~ (x0 = y0))) /\ ((~ ((sqrt x0) = (sqrt y0))) \/ (x0 = y0))).
Definition term82 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => ((sqrt x0) = (sqrt y1)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => (~ ((sqrt x0) = (sqrt y1))) \/ (x0 = y1)) y0)).
Definition term191 := ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term37 := fun y0 : real => ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term120 := ~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term123 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term75 (x0 : real) (x1 : real) := ((sqrt x0) = (sqrt x1)) \/ (~ (x0 = x1)).
Definition term64 := fun y0 : real => forall y1 : real, (((sqrt y0) = (sqrt y1)) \/ (~ (y0 = y1))) /\ ((~ ((sqrt y0) = (sqrt y1))) \/ (y0 = y1)).
Definition term72 (x0 : real) := fun y0 : real => ((sqrt x0) = (sqrt y0)) \/ (~ (x0 = y0)).
Definition term8 := (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1)) -> False.
Definition term130 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term33 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term57 := (exists y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) \/ (exists y0 : real, (~ ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term9 := ~ (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1)).
Definition term21 (x0 : real) := ~ (((sqrt x0) = (real_of_num (NUMERAL (BIT1 0)))) = (x0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term129 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term153 (x0 : real) := (((sqrt x0) = (real_of_num (NUMERAL (BIT1 0)))) /\ ((sqrt x0) = (sqrt x0))) -> (real_of_num (NUMERAL (BIT1 0))) = (sqrt x0).
Definition term29 := fun y0 : real => (((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((~ ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term5 := ((~ (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1)) -> False) -> (~ (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1)) -> False.
Definition term34 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term140 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term189 (x0 : real) := (x0 = (real_of_num (NUMERAL (BIT1 0)))) -> False.
Definition term92 (x0 : real) := (forall y0 : real, ((sqrt x0) = (sqrt y0)) \/ (~ (x0 = y0))) /\ (forall y0 : real, (~ ((sqrt x0) = (sqrt y0))) \/ (x0 = y0)).
Definition term187 (x0 : real) := ((sqrt x0) = (sqrt (real_of_num (NUMERAL (BIT1 0))))) -> x0 = (real_of_num (NUMERAL (BIT1 0))).
Definition term62 (x0 : real) := fun y0 : real => (((sqrt x0) = (sqrt y0)) \/ (~ (x0 = y0))) /\ ((~ ((sqrt x0) = (sqrt y0))) \/ (x0 = y0)).
Definition term154 (x0 : real) := (~ ((real_of_num (NUMERAL (BIT1 0))) = (sqrt x0))) -> (real_of_num (NUMERAL (BIT1 0))) = (sqrt x0).
Definition term84 (x0 : real) := fun y0 : real => (fun y1 : real => ((sqrt x0) = (sqrt y1)) \/ (~ (x0 = y1))) y0.
Definition term174 (x0 : real) (x1 : real) := @eq Prop ((x0 = x1) \/ (~ ((sqrt x0) = (sqrt x1)))).
Definition term48 := @eq Prop (exists y0 : real, (((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((~ ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term47 := @eq Prop (exists y0 : real, ((fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0) \/ ((fun y1 : real => (~ ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0)).
Definition term98 := fun y0 : real => forall y1 : real, (~ ((sqrt y0) = (sqrt y1))) \/ (y0 = y1).
Definition term18 := fun y0 : real => forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1).
Definition term24 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term68 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term167 := ((sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (real_of_num (NUMERAL (BIT1 0))))) /\ ((sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (sqrt (real_of_num (NUMERAL (BIT1 0)))))).
Definition term101 (x0 : real) := (fun y0 : real => forall y1 : real, (~ ((sqrt y0) = (sqrt y1))) \/ (y0 = y1)) x0.
Definition term99 (x0 : real) := (fun y0 : real => forall y1 : real, ((sqrt y0) = (sqrt y1)) \/ (~ (y0 = y1))) x0.
Definition term51 := exists y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term177 (x0 : real) (x1 : real) := imp (~ (~ ((sqrt x0) = (sqrt x1)))).
Definition term2 := (~ (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> False.
Definition term90 (x0 : real) := forall y0 : real, (fun y1 : real => (~ ((sqrt x0) = (sqrt y1))) \/ (x0 = y1)) y0.
Definition term85 (x0 : real) := forall y0 : real, (fun y1 : real => ((sqrt x0) = (sqrt y1)) \/ (~ (x0 = y1))) y0.
Definition term79 (x0 : real) (x1 : real) := (~ ((sqrt x0) = (sqrt x1))) \/ (x0 = x1).
Definition term148 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term103 := fun y0 : real => ((fun y1 : real => forall y2 : real, ((sqrt y1) = (sqrt y2)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, (~ ((sqrt y1) = (sqrt y2))) \/ (y1 = y2)) y0).
Definition term188 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL (BIT1 0))))) -> x0 = (real_of_num (NUMERAL (BIT1 0))).
Definition term22 (x0 : real) := (((sqrt x0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (x0 = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((~ ((sqrt x0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (x0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term134 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term179 (x0 : real) (x1 : real) := ((sqrt x0) = (sqrt x1)) -> x0 = x1.
Definition term186 (x0 : real) := ~ ((sqrt x0) = (sqrt (real_of_num (NUMERAL (BIT1 0))))).
Definition term132 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term7 := (((~ (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1)) -> False) -> (~ (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1)) -> False) -> ((~ (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1)) -> False) -> (~ (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1)) -> False.
Definition term168 := (((sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (real_of_num (NUMERAL (BIT1 0))))) /\ ((sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))))) -> (sqrt (real_of_num (NUMERAL (BIT1 0)))) = (sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))).
Definition term60 := sqrt (real_of_num (NUMERAL (BIT1 0))).
Definition term80 (x0 : real) (x1 : real) := ((fun y0 : real => ((sqrt x0) = (sqrt y0)) \/ (~ (x0 = y0))) x1) /\ ((fun y0 : real => (~ ((sqrt x0) = (sqrt y0))) \/ (x0 = y0)) x1).
Definition term146 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term156 := (~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))))) -> (sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0))).
Definition term46 := fun y0 : real => ((fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0) \/ ((fun y1 : real => (~ ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term20 := fun y0 : real => ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))).
Definition term35 := exists y0 : real, ((fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0) \/ ((fun y1 : real => (~ ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term38 := fun y0 : real => (~ ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0)))).
Definition term39 (x0 : real) := (fun y0 : real => ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) x0.
Definition term45 (x0 : real) := ((fun y0 : real => ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) x0) \/ ((fun y0 : real => (~ ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0))))) x0).
Definition term44 (x0 : real) := (~ ((sqrt x0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (x0 = (real_of_num (NUMERAL (BIT1 0)))).
Definition term40 (x0 : real) := ((sqrt x0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (x0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term175 (x0 : real) (x1 : real) := (~ (~ ((sqrt x0) = (sqrt x1)))) -> x0 = x1.
Definition term94 := forall y0 : real, (forall y1 : real, ((sqrt y0) = (sqrt y1)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (~ ((sqrt y0) = (sqrt y1))) \/ (y0 = y1)).
Definition term160 (x0 : real) (x1 : real) := (x0 = x1) -> (sqrt x0) = (sqrt x1).
Definition term91 (x0 : real) := forall y0 : real, (~ ((sqrt x0) = (sqrt y0))) \/ (x0 = y0).
Definition term170 := ~ ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (sqrt (sqrt (real_of_num (NUMERAL (BIT1 0)))))).
Definition term166 := ~ ((sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (sqrt (real_of_num (NUMERAL (BIT1 0)))))).
Definition term164 := ~ ((sqrt (sqrt (real_of_num (NUMERAL (BIT1 0))))) = (sqrt (real_of_num (NUMERAL (BIT1 0))))).
Definition term151 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term142 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term19 := real_of_num (NUMERAL (BIT1 0)).
Definition term138 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term54 := fun y0 : real => (fun y1 : real => (~ ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0.
Definition term112 := forall y0 : real, (fun y1 : real => forall y2 : real, (~ ((sqrt y1) = (sqrt y2))) \/ (y1 = y2)) y0.
Definition term107 := forall y0 : real, (fun y1 : real => forall y2 : real, ((sqrt y1) = (sqrt y2)) \/ (~ (y1 = y2))) y0.
Definition term1 := forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))).
Definition term147 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term102 (x0 : real) := ((fun y0 : real => forall y1 : real, ((sqrt y0) = (sqrt y1)) \/ (~ (y0 = y1))) x0) /\ ((fun y0 : real => forall y1 : real, (~ ((sqrt y0) = (sqrt y1))) \/ (y0 = y1)) x0).
Definition term81 (x0 : real) := fun y0 : real => ((fun y1 : real => ((sqrt x0) = (sqrt y1)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => (~ ((sqrt x0) = (sqrt y1))) \/ (x0 = y1)) y0).
Definition term89 (x0 : real) := fun y0 : real => (fun y1 : real => (~ ((sqrt x0) = (sqrt y1))) \/ (x0 = y1)) y0.
Definition term16 (x0 : real) := fun y0 : real => ((sqrt x0) = (sqrt y0)) = (x0 = y0).
Definition term162 := sqrt (sqrt (real_of_num (NUMERAL (BIT1 0)))).
Definition term27 (x0 : real) := ~ ((fun y0 : real => ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0))))) x0).
Definition term176 (x0 : real) (x1 : real) := ~ (~ ((sqrt x0) = (sqrt x1))).
Definition term28 := fun y0 : real => ~ ((fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0)))) = (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term56 := exists y0 : real, (~ ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0)))).
Definition term77 (x0 : real) (x1 : real) := and (((sqrt x0) = (sqrt x1)) \/ (~ (x0 = x1))).
Definition term30 := exists y0 : real, (((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) \/ ((~ ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0))))).
Definition term74 (x0 : real) (x1 : real) := (fun y0 : real => ((sqrt x0) = (sqrt y0)) \/ (~ (x0 = y0))) x1.
Definition term69 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term150 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term41 (x0 : real) := or ((fun y0 : real => ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) x0).
Definition term43 (x0 : real) := (fun y0 : real => (~ ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term155 (x0 : real) := ~ ((real_of_num (NUMERAL (BIT1 0))) = (sqrt x0)).
Definition term122 (x0 : real) := @eq Prop (~ ((sqrt x0) = (real_of_num (NUMERAL (BIT1 0))))).
Definition term128 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term157 (x0 : real) (x1 : real) := (~ (~ (x0 = x1))) -> (sqrt x0) = (sqrt x1).
Definition term145 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term76 (x0 : real) (x1 : real) := and ((fun y0 : real => ((sqrt x0) = (sqrt y0)) \/ (~ (x0 = y0))) x1).
Definition term26 (x0 : real) := (fun y0 : real => ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term131 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term53 := or (exists y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term184 (x0 : real) := (((real_of_num (NUMERAL (BIT1 0))) = (sqrt x0)) /\ ((real_of_num (NUMERAL (BIT1 0))) = (sqrt (real_of_num (NUMERAL (BIT1 0)))))) -> (sqrt x0) = (sqrt (real_of_num (NUMERAL (BIT1 0)))).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term159 (x0 : real) (x1 : real) := imp (x0 = x1).
Definition term127 (x0 : real) := ~ ((sqrt x0) = (sqrt x0)).
Definition term86 (x0 : real) := forall y0 : real, ((sqrt x0) = (sqrt y0)) \/ (~ (x0 = y0)).
Definition term95 := forall y0 : real, ((fun y1 : real => forall y2 : real, ((sqrt y1) = (sqrt y2)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, (~ ((sqrt y1) = (sqrt y2))) \/ (y1 = y2)) y0).
Definition term70 (x0 : real) := forall y0 : real, ((fun y1 : real => ((sqrt x0) = (sqrt y1)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => (~ ((sqrt x0) = (sqrt y1))) \/ (x0 = y1)) y0).
Definition term36 := (exists y0 : real, (fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0) \/ (exists y0 : real, (fun y1 : real => (~ ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term124 (x0 : real) := (~ ((sqrt x0) = (real_of_num (NUMERAL (BIT1 0))))) -> (sqrt x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term14 := imp (~ (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term97 := fun y0 : real => forall y1 : real, ((sqrt y0) = (sqrt y1)) \/ (~ (y0 = y1)).
Definition term158 (x0 : real) (x1 : real) := imp (~ (~ (x0 = x1))).
Definition term6 := (((~ (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1)) -> False) -> (~ (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1)) -> False) -> (~ (forall y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) = (y0 = (real_of_num (NUMERAL (BIT1 0)))))) -> ((sqrt (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (NUMERAL (BIT1 0)))) -> (forall y0 : real, forall y1 : real, ((sqrt y0) = (sqrt y1)) = (y0 = y1)) -> False.
Definition term59 := @eq Prop ((exists y0 : real, ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y0 = (real_of_num (NUMERAL (BIT1 0)))))) \/ (exists y0 : real, (~ ((sqrt y0) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y0 = (real_of_num (NUMERAL (BIT1 0)))))).
Definition term58 := @eq Prop ((exists y0 : real, (fun y1 : real => ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (~ (y1 = (real_of_num (NUMERAL (BIT1 0)))))) y0) \/ (exists y0 : real, (fun y1 : real => (~ ((sqrt y1) = (real_of_num (NUMERAL (BIT1 0))))) /\ (y1 = (real_of_num (NUMERAL (BIT1 0))))) y0)).
