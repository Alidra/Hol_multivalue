Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term165 (x0 : real) := imp ((real_inv x0) = (real_of_num (NUMERAL 0))).
Definition term34 (x0 : real) := ~ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = (real_inv x0))).
Definition term50 (x0 : real -> Prop) := ~ (all x0).
Definition term118 (x0 : real) := (fun y0 : real => ~ ((real_of_num (NUMERAL 0)) = (real_inv y0))) x0.
Definition term126 := (~ False) -> False.
Definition term24 := (~ (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)))) -> (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> False.
Definition term175 (x0 : real) := (~ (~ (x0 = (real_of_num (NUMERAL 0))))) -> (real_inv x0) = (real_of_num (NUMERAL 0)).
Definition term122 (x0 : real) := @eq Prop (~ ((real_of_num (NUMERAL 0)) = (real_inv x0))).
Definition term188 := (~ ((real_of_num (NUMERAL 0)) = (real_inv (real_of_num (NUMERAL 0))))) -> (real_of_num (NUMERAL 0)) = (real_inv (real_of_num (NUMERAL 0))).
Definition term147 (x0 : Prop) := ~ (~ x0).
Definition term93 := fun y0 : real => ((real_inv y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0)))).
Definition term9 := real_of_num (NUMERAL 0).
Definition term123 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> real_lt (real_of_num (NUMERAL 0)) x0.
Definition term53 (x0 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0))) x0.
Definition term95 (x0 : real) := (fun y0 : real => ((real_inv y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))) x0.
Definition term109 := and (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))).
Definition term146 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term121 (x0 : real) := @eq Prop ((fun y0 : real => ~ ((real_of_num (NUMERAL 0)) = (real_inv y0))) x0).
Definition term162 (x0 : real) := (~ (~ ((real_inv x0) = (real_of_num (NUMERAL 0))))) -> x0 = (real_of_num (NUMERAL 0)).
Definition term108 := and (forall y0 : real, (fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL 0))) \/ (~ (y1 = (real_of_num (NUMERAL 0))))) y0).
Definition term21 (x0 : Prop) := (~ x0) -> False.
Definition term152 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term29 := ~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))).
Definition term23 := ~ (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0))).
Definition term12 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = (real_inv x0)).
Definition term84 (x0 : real) := (((real_inv x0) = (real_of_num (NUMERAL 0))) \/ (~ (x0 = (real_of_num (NUMERAL 0))))) /\ ((~ ((real_inv x0) = (real_of_num (NUMERAL 0)))) \/ (x0 = (real_of_num (NUMERAL 0)))).
Definition term181 := real_inv (real_of_num (NUMERAL 0)).
Definition term56 := fun y0 : real => (((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = y0)))) \/ (((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y0)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0))).
Definition term45 (x0 : real) := or (((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = (real_inv x0))) /\ (~ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = x0)))).
Definition term11 (x0 : real) := or (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term42 (x0 : real) := and ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = (real_inv x0))).
Definition term156 (x0 : real) := (((real_of_num (NUMERAL 0)) = (real_inv x0)) /\ ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0)))) -> (real_inv x0) = (real_of_num (NUMERAL 0)).
Definition term140 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term92 := (forall y0 : real, (fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL 0))) \/ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) /\ (forall y0 : real, (fun y1 : real => (~ ((real_inv y1) = (real_of_num (NUMERAL 0)))) \/ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term184 := (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_inv (real_of_num (NUMERAL 0))))) -> (real_inv (real_of_num (NUMERAL 0))) = (real_inv (real_of_num (NUMERAL 0))).
Definition term68 (x0 : real) := (fun y0 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y0)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0))) x0.
Definition term169 (x0 : real) := (~ (x0 = x0)) -> x0 = x0.
Definition term116 (x0 : real) := ~ ((real_of_num (NUMERAL 0)) = (real_inv x0)).
Definition term124 (x0 : Prop) := (~ x0) -> x0.
Definition term16 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = x0).
Definition term142 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term183 := ~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term144 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term177 (x0 : real) := imp (~ (~ (x0 = (real_of_num (NUMERAL 0))))).
Definition term138 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term79 := exists y0 : real, (fun y1 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y1)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = y1))) y0.
Definition term74 := exists y0 : real, (fun y1 : real => ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = (real_inv y1))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ ((real_of_num (NUMERAL 0)) = y1)))) y0.
Definition term139 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term76 := or (exists y0 : real, (fun y1 : real => ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = (real_inv y1))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ ((real_of_num (NUMERAL 0)) = y1)))) y0).
Definition term136 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term187 := (((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) /\ ((real_inv (real_of_num (NUMERAL 0))) = (real_inv (real_of_num (NUMERAL 0))))) -> (real_of_num (NUMERAL 0)) = (real_inv (real_of_num (NUMERAL 0))).
Definition term114 (x0 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term168 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term52 := exists y0 : real, ~ ((fun y1 : real => ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = (real_inv y1))) = ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = y1))) y0).
Definition term178 (x0 : real) := imp (x0 = (real_of_num (NUMERAL 0))).
Definition term110 := fun y0 : real => (fun y1 : real => (~ ((real_inv y1) = (real_of_num (NUMERAL 0)))) \/ (y1 = (real_of_num (NUMERAL 0)))) y0.
Definition term20 := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)).
Definition term128 (x0 : real) := (~ ((real_of_num (NUMERAL 0)) = (real_inv x0))) -> (real_of_num (NUMERAL 0)) = (real_inv x0).
Definition term172 (x0 : real) := ((x0 = (real_of_num (NUMERAL 0))) /\ (x0 = x0)) -> (real_of_num (NUMERAL 0)) = x0.
Definition term104 := @eq Prop (forall y0 : real, (((real_inv y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))) /\ ((~ ((real_inv y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0))))).
Definition term103 := @eq Prop (forall y0 : real, ((fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL 0))) \/ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) /\ ((fun y1 : real => (~ ((real_inv y1) = (real_of_num (NUMERAL 0)))) \/ (y1 = (real_of_num (NUMERAL 0)))) y0)).
Definition term127 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term163 (x0 : real) := ~ (~ ((real_inv x0) = (real_of_num (NUMERAL 0)))).
Definition term37 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ (~ ((real_of_num (NUMERAL 0)) = x0)).
Definition term44 (x0 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = (real_inv x0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ (~ ((real_of_num (NUMERAL 0)) = x0))).
Definition term17 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_le (real_of_num (NUMERAL 0)) y0).
Definition term0 (x0 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) x0.
Definition term38 (x0 : real) := and (~ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = (real_inv x0)))).
Definition term186 := ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) /\ ((real_inv (real_of_num (NUMERAL 0))) = (real_inv (real_of_num (NUMERAL 0)))).
Definition term133 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term60 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term81 := (exists y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = y0)))) \/ (exists y0 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y0)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0))).
Definition term112 := forall y0 : real, (~ ((real_inv y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0))).
Definition term19 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) (real_inv y0)) = (real_le (real_of_num (NUMERAL 0)) y0).
Definition term26 := (((~ (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)))) -> (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> False) -> (~ (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)))) -> (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> False) -> (~ (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)))) -> (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> False.
Definition term132 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term98 (x0 : real) := and (((real_inv x0) = (real_of_num (NUMERAL 0))) \/ (~ (x0 = (real_of_num (NUMERAL 0))))).
Definition term61 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term97 (x0 : real) := and ((fun y0 : real => ((real_inv y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))) x0).
Definition term143 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term49 (x0 : real) := ~ (((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = (real_inv x0))) = ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = x0))).
Definition term113 := (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))) /\ (forall y0 : real, (~ ((real_inv y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term14 (x0 : real) := @eq Prop ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = (real_inv x0))).
Definition term129 := (~ ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0)))) -> (real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0)).
Definition term96 (x0 : real) := ((real_inv x0) = (real_of_num (NUMERAL 0))) \/ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term18 := fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)).
Definition term94 := fun y0 : real => (~ ((real_inv y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0))).
Definition term101 (x0 : real) := ((fun y0 : real => ((real_inv y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))) x0) /\ ((fun y0 : real => (~ ((real_inv y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0)))) x0).
Definition term33 := fun y0 : real => ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term105 := fun y0 : real => (fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL 0))) \/ (~ (y1 = (real_of_num (NUMERAL 0))))) y0.
Definition term35 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv x0))).
Definition term164 (x0 : real) := imp (~ (~ ((real_inv x0) = (real_of_num (NUMERAL 0))))).
Definition term179 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> (real_inv x0) = (real_of_num (NUMERAL 0)).
Definition term72 := @eq Prop (exists y0 : real, (((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = y0)))) \/ (((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y0)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)))).
Definition term71 := @eq Prop (exists y0 : real, ((fun y1 : real => ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = (real_inv y1))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ ((real_of_num (NUMERAL 0)) = y1)))) y0) \/ ((fun y1 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y1)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = y1))) y0)).
Definition term189 := ((real_of_num (NUMERAL 0)) = (real_inv (real_of_num (NUMERAL 0)))) -> False.
Definition term51 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term89 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term28 := (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> False.
Definition term3 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) x0.
Definition term43 (x0 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = (real_inv x0))) /\ (~ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = x0))).
Definition term117 := fun y0 : real => ~ ((real_of_num (NUMERAL 0)) = (real_inv y0)).
Definition term15 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term22 := (~ (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)))) -> False.
Definition term111 := forall y0 : real, (fun y1 : real => (~ ((real_inv y1) = (real_of_num (NUMERAL 0)))) \/ (y1 = (real_of_num (NUMERAL 0)))) y0.
Definition term106 := forall y0 : real, (fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL 0))) \/ (~ (y1 = (real_of_num (NUMERAL 0))))) y0.
Definition term46 (x0 : real) := or (((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = (real_inv x0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ (~ ((real_of_num (NUMERAL 0)) = x0)))).
Definition term151 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term180 := ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))) -> (real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)).
Definition term185 := ~ ((real_inv (real_of_num (NUMERAL 0))) = (real_inv (real_of_num (NUMERAL 0)))).
Definition term36 (x0 : real) := ~ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = x0)).
Definition term173 (x0 : real) := (~ ((real_of_num (NUMERAL 0)) = x0)) -> (real_of_num (NUMERAL 0)) = x0.
Definition term137 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term135 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term149 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term8 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_inv x0)) \/ ((real_of_num (NUMERAL 0)) = (real_inv x0)).
Definition term174 (x0 : real) := ((real_of_num (NUMERAL 0)) = x0) -> False.
Definition term48 (x0 : real) := (((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = (real_inv x0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ (~ ((real_of_num (NUMERAL 0)) = x0)))) \/ (((~ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv x0)))) /\ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = x0))).
Definition term155 (x0 : real) := ((real_of_num (NUMERAL 0)) = (real_inv x0)) /\ ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))).
Definition term70 := fun y0 : real => ((fun y1 : real => ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = (real_inv y1))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ ((real_of_num (NUMERAL 0)) = y1)))) y0) \/ ((fun y1 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y1)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = y1))) y0).
Definition term40 (x0 : real) := (~ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = (real_inv x0)))) /\ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = x0)).
Definition term62 := exists y0 : real, ((fun y1 : real => ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = (real_inv y1))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ ((real_of_num (NUMERAL 0)) = y1)))) y0) \/ ((fun y1 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y1)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = y1))) y0).
Definition term2 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term167 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> x0 = (real_of_num (NUMERAL 0)).
Definition term39 (x0 : real) := and ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv x0)))).
Definition term182 := (~ ((real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))) -> (real_inv (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)).
Definition term160 (x0 : real) := @eq Prop ((~ ((real_inv x0) = (real_of_num (NUMERAL 0)))) \/ (x0 = (real_of_num (NUMERAL 0)))).
Definition term69 (x0 : real) := ((fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = y0)))) x0) \/ ((fun y0 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y0)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0))) x0).
Definition term120 := ~ ((real_of_num (NUMERAL 0)) = (real_inv (real_of_num (NUMERAL 0)))).
Definition term100 (x0 : real) := (~ ((real_inv x0) = (real_of_num (NUMERAL 0)))) \/ (x0 = (real_of_num (NUMERAL 0))).
Definition term115 (x0 : real) := ~ ((real_of_num (NUMERAL 0)) = x0).
Definition term154 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term145 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term107 := forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0)))).
Definition term141 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term99 (x0 : real) := (fun y0 : real => (~ ((real_inv y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0)))) x0.
Definition term6 (x0 : real) (x1 : real) := (real_lt x0 x1) \/ (x0 = x1).
Definition term78 := fun y0 : real => (fun y1 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y1)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = y1))) y0.
Definition term73 := fun y0 : real => (fun y1 : real => ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = (real_inv y1))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ ((real_of_num (NUMERAL 0)) = y1)))) y0.
Definition term5 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) = ((real_lt x0 y0) \/ (x0 = y0))) x1.
Definition term32 := (~ (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)))) -> ~ (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))).
Definition term75 := exists y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = y0))).
Definition term30 := forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term150 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term64 := fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = y0))).
Definition term170 (x0 : real) := ~ (x0 = x0).
Definition term102 := fun y0 : real => ((fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL 0))) \/ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) /\ ((fun y1 : real => (~ ((real_inv y1) = (real_of_num (NUMERAL 0)))) \/ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term159 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (~ ((real_inv x0) = (real_of_num (NUMERAL 0)))).
Definition term86 := forall y0 : real, (((real_inv y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))) /\ ((~ ((real_inv y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term158 (x0 : real) := ~ ((real_inv x0) = (real_of_num (NUMERAL 0))).
Definition term54 (x0 : real) := ~ ((fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0))) x0).
Definition term1 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (real_inv x0).
Definition term161 (x0 : real) := @eq Prop ((x0 = (real_of_num (NUMERAL 0))) \/ (~ ((real_inv x0) = (real_of_num (NUMERAL 0))))).
Definition term55 := fun y0 : real => ~ ((fun y1 : real => ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = (real_inv y1))) = ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = y1))) y0).
Definition term57 := exists y0 : real, (((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = y0)))) \/ (((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y0)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0))).
Definition term66 (x0 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = y0)))) x0.
Definition term90 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term65 := fun y0 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y0)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)).
Definition term153 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term85 := fun y0 : real => (((real_inv y0) = (real_of_num (NUMERAL 0))) \/ (~ (y0 = (real_of_num (NUMERAL 0))))) /\ ((~ ((real_inv y0) = (real_of_num (NUMERAL 0)))) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term67 (x0 : real) := or ((fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = y0)))) x0).
Definition term119 := (fun y0 : real => ~ ((real_of_num (NUMERAL 0)) = (real_inv y0))) (real_of_num (NUMERAL 0)).
Definition term7 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_inv x0).
Definition term4 (x0 : real) := forall y0 : real, (real_le x0 y0) = ((real_lt x0 y0) \/ (x0 = y0)).
Definition term25 := ((~ (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)))) -> (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> False) -> (~ (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)))) -> (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> False.
Definition term131 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term148 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term27 := (((~ (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)))) -> (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> False) -> (~ (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)))) -> (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> False) -> ((~ (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)))) -> (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> False) -> (~ (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)))) -> (forall y0 : real, ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) -> False.
Definition term171 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) /\ (x0 = x0).
Definition term10 (x0 : real) := or (real_lt (real_of_num (NUMERAL 0)) (real_inv x0)).
Definition term47 (x0 : real) := (((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = (real_inv x0))) /\ (~ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = x0)))) \/ ((~ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = (real_inv x0)))) /\ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = x0))).
Definition term134 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term41 (x0 : real) := ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv x0)))) /\ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ ((real_of_num (NUMERAL 0)) = x0)).
Definition term13 (x0 : real) := @eq Prop (real_le (real_of_num (NUMERAL 0)) (real_inv x0)).
Definition term77 := or (exists y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = y0)))).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term91 := forall y0 : real, ((fun y1 : real => ((real_inv y1) = (real_of_num (NUMERAL 0))) \/ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) /\ ((fun y1 : real => (~ ((real_inv y1) = (real_of_num (NUMERAL 0)))) \/ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term80 := exists y0 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y0)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)).
Definition term166 (x0 : real) := ((real_inv x0) = (real_of_num (NUMERAL 0))) -> x0 = (real_of_num (NUMERAL 0)).
Definition term125 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> False.
Definition term176 (x0 : real) := ~ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term63 := (exists y0 : real, (fun y1 : real => ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = (real_inv y1))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ ((real_of_num (NUMERAL 0)) = y1)))) y0) \/ (exists y0 : real, (fun y1 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y1)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = y1))) y0).
Definition term31 := imp (~ (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)))).
Definition term130 := ~ ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))).
Definition term157 (x0 : real) := (~ ((real_inv x0) = (real_of_num (NUMERAL 0)))) -> (real_inv x0) = (real_of_num (NUMERAL 0)).
Definition term83 := @eq Prop ((exists y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = (real_inv y0))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = y0)))) \/ (exists y0 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y0)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y0) \/ ((real_of_num (NUMERAL 0)) = y0)))).
Definition term82 := @eq Prop ((exists y0 : real, (fun y1 : real => ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = (real_inv y1))) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ ((real_of_num (NUMERAL 0)) = y1)))) y0) \/ (exists y0 : real, (fun y1 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ ((real_of_num (NUMERAL 0)) = (real_inv y1)))) /\ ((real_lt (real_of_num (NUMERAL 0)) y1) \/ ((real_of_num (NUMERAL 0)) = y1))) y0)).
