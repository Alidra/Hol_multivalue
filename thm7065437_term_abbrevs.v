Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term215 (x0 : real) := ~ ((real_add x0 (real_of_num (NUMERAL 0))) = x0).
Definition term70 (x0 : real -> Prop) := ~ (all x0).
Definition term251 := (~ False) -> False.
Definition term221 (x0 : real) := (~ ((real_add (real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0)))) -> (real_add (real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0)).
Definition term59 (x0 : real) := @eq Prop ((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0)).
Definition term24 (x0 : real) (x1 : real) := (fun y0 : real => (real_add y0 x0) = y0) x1.
Definition term21 (x0 : real) (x1 : real) := (fun y0 : real => (real_add x0 y0) = y0) x1.
Definition term123 := fun y0 : real => (fun y1 : real => ((forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) y0.
Definition term239 (x0 : Prop) := ~ (~ x0).
Definition term250 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> False.
Definition term4 := real_of_num (NUMERAL 0).
Definition term168 (x0 : real) := fun y0 : real => ((fun y1 : real => (~ ((real_add x0 y1) = y1)) \/ (~ ((real_add y1 x0) = y1))) y0) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term238 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term52 := (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> False.
Definition term68 := fun y0 : real => (real_add y0 (real_of_num (NUMERAL 0))) = y0.
Definition term35 (x0 : real) := and (forall y0 : real, (fun y1 : real => (real_add x0 y1) = y1) y0).
Definition term5 (x0 : Prop) := (~ x0) -> False.
Definition term28 (x0 : real) := fun y0 : real => ((real_add x0 y0) = y0) /\ ((real_add y0 x0) = y0).
Definition term244 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term62 := ~ (forall y0 : real, ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) = (y0 = (real_of_num (NUMERAL 0)))).
Definition term49 := ~ (forall y0 : real, ((fun y1 : real => (forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0)))).
Definition term8 := ~ (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0)))).
Definition term115 := fun y0 : real => ((exists y1 : real, ~ ((real_add y0 y1) = y1)) \/ (exists y1 : real, ~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0))).
Definition term139 (x0 : real) := fun y0 : real => (fun y1 : real => ~ ((real_add y1 x0) = y1)) y0.
Definition term135 (x0 : real) := fun y0 : real => (fun y1 : real => ~ ((real_add x0 y1) = y1)) y0.
Definition term155 (x0 : real -> Prop) (x1 : Prop) := exists y0 : real, (x0 y0) /\ x1.
Definition term98 (x0 : real) := or (((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0)) /\ (~ (x0 = (real_of_num (NUMERAL 0))))).
Definition term170 (x0 : real) := exists y0 : real, ((~ ((real_add x0 y0) = y0)) \/ (~ ((real_add y0 x0) = y0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term130 := exists y0 : real, ((exists y1 : real, ~ ((real_add y0 y1) = y1)) \/ (exists y1 : real, ~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0))).
Definition term79 (x0 : real) := ~ (forall y0 : real, (real_add y0 x0) = y0).
Definition term72 (x0 : real) := ~ (forall y0 : real, (real_add x0 y0) = y0).
Definition term53 := ~ (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0).
Definition term232 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term144 (x0 : real) (x1 : real) := or (~ ((real_add x0 x1) = x1)).
Definition term116 (x0 : real) := (fun y0 : real => ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) x0.
Definition term18 (x0 : real) := (forall y0 : real, (fun y1 : real => (real_add x0 y1) = y1) y0) /\ (forall y0 : real, (fun y1 : real => (real_add y1 x0) = y1) y0).
Definition term45 (x0 : real) := @eq Prop ((fun y0 : real => (forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) x0).
Definition term196 (x0 : real) := @eq Prop ((((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0)) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) \/ (exists y0 : real, ((~ ((real_add x0 y0) = y0)) \/ (~ ((real_add y0 x0) = y0))) /\ (x0 = (real_of_num (NUMERAL 0))))).
Definition term195 (x0 : real) := @eq Prop ((((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0)) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) \/ (exists y0 : real, (fun y1 : real => ((~ ((real_add x0 y1) = y1)) \/ (~ ((real_add y1 x0) = y1))) /\ (x0 = (real_of_num (NUMERAL 0)))) y0)).
Definition term219 (x0 : real) := (~ ((real_add (real_of_num (NUMERAL 0)) x0) = x0)) -> (real_add (real_of_num (NUMERAL 0)) x0) = x0.
Definition term147 (x0 : real) := fun y0 : real => ((fun y1 : real => ~ ((real_add x0 y1) = y1)) y0) \/ ((fun y1 : real => ~ ((real_add y1 x0) = y1)) y0).
Definition term220 (x0 : Prop) := (~ x0) -> x0.
Definition term67 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term10 := ((~ (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))))) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> False) -> (~ (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))))) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> False.
Definition term234 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term36 (x0 : real) := and (forall y0 : real, (real_add x0 y0) = y0).
Definition term236 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term230 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term194 (x0 : real) := exists y0 : real, (fun y1 : real => ((~ ((real_add x0 y1) = y1)) \/ (~ ((real_add y1 x0) = y1))) /\ (x0 = (real_of_num (NUMERAL 0)))) y0.
Definition term160 (x0 : real) := exists y0 : real, (fun y1 : real => (~ ((real_add x0 y1) = y1)) \/ (~ ((real_add y1 x0) = y1))) y0.
Definition term129 := exists y0 : real, (fun y1 : real => ((exists y2 : real, ~ ((real_add y1 y2) = y2)) \/ (exists y2 : real, ~ ((real_add y2 y1) = y2))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0.
Definition term124 := exists y0 : real, (fun y1 : real => ((forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) y0.
Definition term86 (x0 : real) := or (~ (forall y0 : real, (real_add x0 y0) = y0)).
Definition term173 := (exists y0 : real, ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) \/ (exists y0 : real, exists y1 : real, ((~ ((real_add y0 y1) = y1)) \/ (~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0)))).
Definition term231 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term200 (x0 : real) := fun y0 : real => (((forall y1 : real, (real_add x0 y1) = y1) /\ (forall y1 : real, (real_add y1 x0) = y1)) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) \/ (((~ ((real_add x0 y0) = y0)) \/ (~ ((real_add y0 x0) = y0))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term38 (x0 : real) := forall y0 : real, (fun y1 : real => (real_add y1 x0) = y1) y0.
Definition term33 (x0 : real) := forall y0 : real, (fun y1 : real => (real_add x0 y1) = y1) y0.
Definition term203 := exists y0 : real, exists y1 : real, (((forall y2 : real, (real_add y0 y2) = y2) /\ (forall y2 : real, (real_add y2 y0) = y2)) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) \/ (((~ ((real_add y0 y1) = y1)) \/ (~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0)))).
Definition term172 := exists y0 : real, exists y1 : real, ((~ ((real_add y0 y1) = y1)) \/ (~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0))).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term137 (x0 : real) := or (exists y0 : real, (fun y1 : real => ~ ((real_add x0 y1) = y1)) y0).
Definition term126 := or (exists y0 : real, (fun y1 : real => ((forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) y0).
Definition term37 (x0 : real) := fun y0 : real => (fun y1 : real => (real_add y1 x0) = y1) y0.
Definition term32 (x0 : real) := fun y0 : real => (fun y1 : real => (real_add x0 y1) = y1) y0.
Definition term228 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term64 := (~ (forall y0 : real, ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) = (y0 = (real_of_num (NUMERAL 0))))) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> ~ (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0).
Definition term58 := (~ (forall y0 : real, ((fun y1 : real => (forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))))) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> ~ (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0).
Definition term157 (x0 : real) := exists y0 : real, ((fun y1 : real => (~ ((real_add x0 y1) = y1)) \/ (~ ((real_add y1 x0) = y1))) y0) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term1 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (x0 y0) = (y0 = x1)) -> (@ε real x0) = x1.
Definition term254 (x0 : real) := ((real_add x0 (real_of_num (NUMERAL 0))) = x0) -> False.
Definition term91 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term102 := exists y0 : real, ~ ((fun y1 : real => ((forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) = (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term80 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_add y1 x0) = y1) y0).
Definition term73 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_add x0 y1) = y1) y0).
Definition term214 (x0 : real) := (fun y0 : real => ~ ((real_add x0 y0) = x0)) (real_of_num (NUMERAL 0)).
Definition term208 (x0 : real) := (fun y0 : real => ~ ((real_add y0 x0) = x0)) (real_of_num (NUMERAL 0)).
Definition term25 (x0 : real) (x1 : real) := ((fun y0 : real => (real_add x0 y0) = y0) x1) /\ ((fun y0 : real => (real_add y0 x0) = y0) x1).
Definition term176 (x0 : real) := (fun y0 : real => exists y1 : real, ((~ ((real_add y0 y1) = y1)) \/ (~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0)))) x0.
Definition term197 (x0 : real) (x1 : real) := (((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0)) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) \/ ((fun y0 : real => ((~ ((real_add x0 y0) = y0)) \/ (~ ((real_add y0 x0) = y0))) /\ (x0 = (real_of_num (NUMERAL 0)))) x1).
Definition term44 (x0 : real) := @eq Prop ((fun y0 : real => forall y1 : real, ((real_add y0 y1) = y1) /\ ((real_add y1 y0) = y1)) x0).
Definition term29 (x0 : real) := forall y0 : real, ((real_add x0 y0) = y0) /\ ((real_add y0 x0) = y0).
Definition term191 (x0 : real) := exists y0 : real, (((forall y1 : real, (real_add x0 y1) = y1) /\ (forall y1 : real, (real_add y1 x0) = y1)) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) \/ ((fun y1 : real => ((~ ((real_add x0 y1) = y1)) \/ (~ ((real_add y1 x0) = y1))) /\ (x0 = (real_of_num (NUMERAL 0)))) y0).
Definition term31 (x0 : real) := @eq Prop (forall y0 : real, ((real_add x0 y0) = y0) /\ ((real_add y0 x0) = y0)).
Definition term30 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (real_add x0 y1) = y1) y0) /\ ((fun y1 : real => (real_add y1 x0) = y1) y0)).
Definition term218 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term96 (x0 : real) := and ((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0)).
Definition term204 (x0 : real) := (fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term114 := fun y0 : real => ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) /\ (~ (y0 = (real_of_num (NUMERAL 0)))).
Definition term198 (x0 : real) (x1 : real) := (((forall y0 : real, (real_add x1 y0) = y0) /\ (forall y0 : real, (real_add y0 x1) = y0)) /\ (~ (x1 = (real_of_num (NUMERAL 0))))) \/ (((~ ((real_add x1 x0) = x0)) \/ (~ ((real_add x0 x1) = x0))) /\ (x1 = (real_of_num (NUMERAL 0)))).
Definition term40 (x0 : real) := (forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0).
Definition term225 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term110 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term151 (x0 : real) := (exists y0 : real, (~ ((real_add x0 y0) = y0)) \/ (~ ((real_add y0 x0) = y0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term131 := (exists y0 : real, ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) \/ (exists y0 : real, ((exists y1 : real, ~ ((real_add y0 y1) = y1)) \/ (exists y1 : real, ~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0)))).
Definition term247 (x0 : real) := ((real_add (real_of_num (NUMERAL 0)) x0) = x0) /\ ((real_add (real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0))).
Definition term148 (x0 : real) := fun y0 : real => (~ ((real_add x0 y0) = y0)) \/ (~ ((real_add y0 x0) = y0)).
Definition term83 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_add y1 x0) = y1) y0).
Definition term76 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_add x0 y1) = y1) y0).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (forall y0 : a0, (x0 y0) = (y0 = x1)) -> (@ε a0 x0) = x1.
Definition term224 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term185 := exists y0 : real, (((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) \/ (exists y1 : real, ((~ ((real_add y0 y1) = y1)) \/ (~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0)))).
Definition term177 := fun y0 : real => (fun y1 : real => exists y2 : real, ((~ ((real_add y1 y2) = y2)) \/ (~ ((real_add y2 y1) = y2))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0.
Definition term187 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term111 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term235 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term181 (x0 : real) := ((fun y0 : real => ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) x0) \/ ((fun y0 : real => exists y1 : real, ((~ ((real_add y0 y1) = y1)) \/ (~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0)))) x0).
Definition term145 (x0 : real) (x1 : real) := ((fun y0 : real => ~ ((real_add x0 y0) = y0)) x1) \/ ((fun y0 : real => ~ ((real_add y0 x0) = y0)) x1).
Definition term186 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term153 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term202 := fun y0 : real => exists y1 : real, (((forall y2 : real, (real_add y0 y2) = y2) /\ (forall y2 : real, (real_add y2 y0) = y2)) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) \/ (((~ ((real_add y0 y1) = y1)) \/ (~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0)))).
Definition term171 := fun y0 : real => exists y1 : real, ((~ ((real_add y0 y1) = y1)) \/ (~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0))).
Definition term54 := forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0.
Definition term39 (x0 : real) := forall y0 : real, (real_add y0 x0) = y0.
Definition term34 (x0 : real) := forall y0 : real, (real_add x0 y0) = y0.
Definition term85 (x0 : real) := exists y0 : real, ~ ((real_add y0 x0) = y0).
Definition term78 (x0 : real) := exists y0 : real, ~ ((real_add x0 y0) = y0).
Definition term156 (x0 : real) := (exists y0 : real, (fun y1 : real => (~ ((real_add x0 y1) = y1)) \/ (~ ((real_add y1 x0) = y1))) y0) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term57 := (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> ~ (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0).
Definition term165 (x0 : real) (x1 : real) := and ((~ ((real_add x0 x1) = x1)) \/ (~ ((real_add x1 x0) = x1))).
Definition term159 (x0 : real) := fun y0 : real => (fun y1 : real => (~ ((real_add x0 y1) = y1)) \/ (~ ((real_add y1 x0) = y1))) y0.
Definition term167 (x0 : real) (x1 : real) := ((~ ((real_add x1 x0) = x0)) \/ (~ ((real_add x0 x1) = x0))) /\ (x1 = (real_of_num (NUMERAL 0))).
Definition term11 := (((~ (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))))) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> False) -> (~ (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))))) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> False) -> (~ (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))))) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> False.
Definition term212 (x0 : real) := fun y0 : real => ~ ((real_add x0 y0) = x0).
Definition term206 (x0 : real) := fun y0 : real => ~ ((real_add y0 x0) = x0).
Definition term122 := @eq Prop (exists y0 : real, (((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) \/ (((exists y1 : real, ~ ((real_add y0 y1) = y1)) \/ (exists y1 : real, ~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0))))).
Definition term121 := @eq Prop (exists y0 : real, ((fun y1 : real => ((forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) \/ ((fun y1 : real => ((exists y2 : real, ~ ((real_add y1 y2) = y2)) \/ (exists y2 : real, ~ ((real_add y2 y1) = y2))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0)).
Definition term169 (x0 : real) := fun y0 : real => ((~ ((real_add x0 y0) = y0)) \/ (~ ((real_add y0 x0) = y0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term255 := @ε real (fun y0 : real => forall y1 : real, ((real_add y0 y1) = y1) /\ ((real_add y1 y0) = y1)).
Definition term3 := fun y0 : real => forall y1 : real, ((real_add y0 y1) = y1) /\ ((real_add y1 y0) = y1).
Definition term213 (x0 : real) (x1 : real) := (fun y0 : real => ~ ((real_add x0 y0) = x0)) x1.
Definition term207 (x0 : real) (x1 : real) := (fun y0 : real => ~ ((real_add y0 x0) = x0)) x1.
Definition term71 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term15 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term56 := (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> False.
Definition term42 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_add y0 y1) = y1) /\ ((real_add y1 y0) = y1)) x0.
Definition term41 := fun y0 : real => (forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1).
Definition term188 (x0 : Prop) (x1 : real -> Prop) := x0 \/ (exists y0 : real, x1 y0).
Definition term248 (x0 : real) := (((real_add (real_of_num (NUMERAL 0)) x0) = x0) /\ ((real_add (real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0)))) -> x0 = (real_of_num (NUMERAL 0)).
Definition term92 (x0 : real) := and (~ ((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0))).
Definition term125 := exists y0 : real, ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) /\ (~ (y0 = (real_of_num (NUMERAL 0)))).
Definition term217 (x0 : real) (x1 : real) := @eq Prop (~ ((real_add x1 x0) = x1)).
Definition term211 (x0 : real) (x1 : real) := @eq Prop (~ ((real_add x0 x1) = x1)).
Definition term60 := fun y0 : real => ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) = (y0 = (real_of_num (NUMERAL 0))).
Definition term140 (x0 : real) := exists y0 : real, (fun y1 : real => ~ ((real_add y1 x0) = y1)) y0.
Definition term136 (x0 : real) := exists y0 : real, (fun y1 : real => ~ ((real_add x0 y1) = y1)) y0.
Definition term7 := (~ (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))))) -> False.
Definition term89 (x0 : real) := (exists y0 : real, ~ ((real_add x0 y0) = y0)) \/ (exists y0 : real, ~ ((real_add y0 x0) = y0)).
Definition term243 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term19 (x0 : real) := fun y0 : real => (real_add x0 y0) = y0.
Definition term190 (x0 : real) := (((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0)) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) \/ (exists y0 : real, (fun y1 : real => ((~ ((real_add x0 y1) = y1)) \/ (~ ((real_add y1 x0) = y1))) /\ (x0 = (real_of_num (NUMERAL 0)))) y0).
Definition term26 (x0 : real) (x1 : real) := ((real_add x0 x1) = x1) /\ ((real_add x1 x0) = x1).
Definition term143 (x0 : real) (x1 : real) := or ((fun y0 : real => ~ ((real_add x0 y0) = y0)) x1).
Definition term2 := (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0)))) -> (@ε real (fun y0 : real => forall y1 : real, ((real_add y0 y1) = y1) /\ ((real_add y1 y0) = y1))) = (real_of_num (NUMERAL 0)).
Definition term99 (x0 : real) := (((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0)) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) \/ ((~ ((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term229 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term227 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term97 (x0 : real) := ((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0)) /\ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term12 := (((~ (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))))) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> False) -> (~ (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))))) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> False) -> ((~ (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))))) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> False) -> (~ (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))))) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> False.
Definition term90 (x0 : real) := ~ ((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0)).
Definition term241 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term81 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_add y0 x0) = y0) x1).
Definition term74 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_add x0 y0) = y0) x1).
Definition term158 (x0 : real) (x1 : real) := (fun y0 : real => (~ ((real_add x0 y0) = y0)) \/ (~ ((real_add y0 x0) = y0))) x1.
Definition term82 (x0 : real) (x1 : real) := ~ ((real_add x1 x0) = x1).
Definition term75 (x0 : real) (x1 : real) := ~ ((real_add x0 x1) = x1).
Definition term120 := fun y0 : real => ((fun y1 : real => ((forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) \/ ((fun y1 : real => ((exists y2 : real, ~ ((real_add y1 y2) = y2)) \/ (exists y2 : real, ~ ((real_add y2 y1) = y2))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term87 (x0 : real) := or (exists y0 : real, ~ ((real_add x0 y0) = y0)).
Definition term93 (x0 : real) := and ((exists y0 : real, ~ ((real_add x0 y0) = y0)) \/ (exists y0 : real, ~ ((real_add y0 x0) = y0))).
Definition term253 (x0 : real) := (~ ((real_add x0 (real_of_num (NUMERAL 0))) = x0)) -> (real_add x0 (real_of_num (NUMERAL 0))) = x0.
Definition term55 := imp (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0).
Definition term175 := exists y0 : real, ((fun y1 : real => ((forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) \/ ((fun y1 : real => exists y2 : real, ((~ ((real_add y1 y2) = y2)) \/ (~ ((real_add y2 y1) = y2))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term133 (x0 : real) := exists y0 : real, ((fun y1 : real => ~ ((real_add x0 y1) = y1)) y0) \/ ((fun y1 : real => ~ ((real_add y1 x0) = y1)) y0).
Definition term112 := exists y0 : real, ((fun y1 : real => ((forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) \/ ((fun y1 : real => ((exists y2 : real, ~ ((real_add y1 y2) = y2)) \/ (exists y2 : real, ~ ((real_add y2 y1) = y2))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term23 (x0 : real) (x1 : real) := and ((real_add x0 x1) = x1).
Definition term118 (x0 : real) := (fun y0 : real => ((exists y1 : real, ~ ((real_add y0 y1) = y1)) \/ (exists y1 : real, ~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0)))) x0.
Definition term189 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 \/ (x1 y0).
Definition term27 (x0 : real) := fun y0 : real => ((fun y1 : real => (real_add x0 y1) = y1) y0) /\ ((fun y1 : real => (real_add y1 x0) = y1) y0).
Definition term154 (x0 : real -> Prop) (x1 : Prop) := (exists y0 : real, x0 y0) /\ x1.
Definition term249 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> x0 = (real_of_num (NUMERAL 0)).
Definition term106 := fun y0 : real => (((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) \/ (((exists y1 : real, ~ ((real_add y0 y1) = y1)) \/ (exists y1 : real, ~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0)))).
Definition term84 (x0 : real) := fun y0 : real => ~ ((real_add y0 x0) = y0).
Definition term77 (x0 : real) := fun y0 : real => ~ ((real_add x0 y0) = y0).
Definition term43 (x0 : real) := (fun y0 : real => (forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) x0.
Definition term95 (x0 : real) := ((exists y0 : real, ~ ((real_add x0 y0) = y0)) \/ (exists y0 : real, ~ ((real_add y0 x0) = y0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term119 (x0 : real) := ((fun y0 : real => ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) x0) \/ ((fun y0 : real => ((exists y1 : real, ~ ((real_add y0 y1) = y1)) \/ (exists y1 : real, ~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0)))) x0).
Definition term47 := fun y0 : real => ((fun y1 : real => (forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))).
Definition term46 := fun y0 : real => ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))).
Definition term69 := forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0.
Definition term182 (x0 : real) := (((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0)) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) \/ (exists y0 : real, ((~ ((real_add x0 y0) = y0)) \/ (~ ((real_add y0 x0) = y0))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term65 (x0 : real) := real_add (real_of_num (NUMERAL 0)) x0.
Definition term246 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term237 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term222 (x0 : real) := ~ ((real_add (real_of_num (NUMERAL 0)) x0) = (real_of_num (NUMERAL 0))).
Definition term233 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term216 (x0 : real) (x1 : real) := @eq Prop ((fun y0 : real => ~ ((real_add x0 y0) = x0)) x1).
Definition term210 (x0 : real) (x1 : real) := @eq Prop ((fun y0 : real => ~ ((real_add y0 x0) = x0)) x1).
Definition term161 (x0 : real) := and (exists y0 : real, (fun y1 : real => (~ ((real_add x0 y1) = y1)) \/ (~ ((real_add y1 x0) = y1))) y0).
Definition term193 (x0 : real) := fun y0 : real => (fun y1 : real => ((~ ((real_add x0 y1) = y1)) \/ (~ ((real_add y1 x0) = y1))) /\ (x0 = (real_of_num (NUMERAL 0)))) y0.
Definition term128 := fun y0 : real => (fun y1 : real => ((exists y2 : real, ~ ((real_add y1 y2) = y2)) \/ (exists y2 : real, ~ ((real_add y2 y1) = y2))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0.
Definition term209 (x0 : real) := ~ ((real_add (real_of_num (NUMERAL 0)) x0) = x0).
Definition term61 := forall y0 : real, ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) = (y0 = (real_of_num (NUMERAL 0))).
Definition term242 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term100 (x0 : real) := (((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0)) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) \/ (((exists y0 : real, ~ ((real_add x0 y0) = y0)) \/ (exists y0 : real, ~ ((real_add y0 x0) = y0))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term88 (x0 : real) := (~ (forall y0 : real, (real_add x0 y0) = y0)) \/ (~ (forall y0 : real, (real_add y0 x0) = y0)).
Definition term104 (x0 : real) := ~ ((fun y0 : real => ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) = (y0 = (real_of_num (NUMERAL 0)))) x0).
Definition term101 (x0 : real) := ~ (((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0)) = (x0 = (real_of_num (NUMERAL 0)))).
Definition term105 := fun y0 : real => ~ ((fun y1 : real => ((forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) = (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term201 (x0 : real) := exists y0 : real, (((forall y1 : real, (real_add x0 y1) = y1) /\ (forall y1 : real, (real_add y1 x0) = y1)) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) \/ (((~ ((real_add x0 y0) = y0)) \/ (~ ((real_add y0 x0) = y0))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term107 := exists y0 : real, (((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) \/ (((exists y1 : real, ~ ((real_add y0 y1) = y1)) \/ (exists y1 : real, ~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0)))).
Definition term16 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term166 (x0 : real) (x1 : real) := ((fun y0 : real => (~ ((real_add x1 y0) = y0)) \/ (~ ((real_add y0 x1) = y0))) x0) /\ (x1 = (real_of_num (NUMERAL 0))).
Definition term149 (x0 : real) := exists y0 : real, (~ ((real_add x0 y0) = y0)) \/ (~ ((real_add y0 x0) = y0)).
Definition term245 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term117 (x0 : real) := or ((fun y0 : real => ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) x0).
Definition term22 (x0 : real) (x1 : real) := and ((fun y0 : real => (real_add x0 y0) = y0) x1).
Definition term20 (x0 : real) := fun y0 : real => (real_add y0 x0) = y0.
Definition term252 (x0 : real) := ((real_add (real_of_num (NUMERAL 0)) x0) = x0) -> False.
Definition term184 := fun y0 : real => (((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) \/ (exists y1 : real, ((~ ((real_add y0 y1) = y1)) \/ (~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0)))).
Definition term48 := forall y0 : real, ((fun y1 : real => (forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))).
Definition term6 := forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))).
Definition term152 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term223 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term205 (x0 : real) := (fun y0 : real => (real_add y0 (real_of_num (NUMERAL 0))) = y0) x0.
Definition term240 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term164 (x0 : real) (x1 : real) := and ((fun y0 : real => (~ ((real_add x0 y0) = y0)) \/ (~ ((real_add y0 x0) = y0))) x1).
Definition term226 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term192 (x0 : real) (x1 : real) := (fun y0 : real => ((~ ((real_add x0 y0) = y0)) \/ (~ ((real_add y0 x0) = y0))) /\ (x0 = (real_of_num (NUMERAL 0)))) x1.
Definition term163 (x0 : real) := @eq Prop ((exists y0 : real, (~ ((real_add x0 y0) = y0)) \/ (~ ((real_add y0 x0) = y0))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term162 (x0 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => (~ ((real_add x0 y1) = y1)) \/ (~ ((real_add y1 x0) = y1))) y0) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term183 := fun y0 : real => ((fun y1 : real => ((forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) \/ ((fun y1 : real => exists y2 : real, ((~ ((real_add y1 y2) = y2)) \/ (~ ((real_add y2 y1) = y2))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term127 := or (exists y0 : real, ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) /\ (~ (y0 = (real_of_num (NUMERAL 0))))).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term9 := (~ (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))))) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) -> False.
Definition term150 (x0 : real) := and (exists y0 : real, (~ ((real_add x0 y0) = y0)) \/ (~ ((real_add y0 x0) = y0))).
Definition term103 (x0 : real) := (fun y0 : real => ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) = (y0 = (real_of_num (NUMERAL 0)))) x0.
Definition term146 (x0 : real) (x1 : real) := (~ ((real_add x0 x1) = x1)) \/ (~ ((real_add x1 x0) = x1)).
Definition term138 (x0 : real) (x1 : real) := (fun y0 : real => ~ ((real_add y0 x0) = y0)) x1.
Definition term134 (x0 : real) (x1 : real) := (fun y0 : real => ~ ((real_add x0 y0) = y0)) x1.
Definition term17 (x0 : real) := forall y0 : real, ((fun y1 : real => (real_add x0 y1) = y1) y0) /\ ((fun y1 : real => (real_add y1 x0) = y1) y0).
Definition term94 (x0 : real) := (~ ((forall y0 : real, (real_add x0 y0) = y0) /\ (forall y0 : real, (real_add y0 x0) = y0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term174 := (exists y0 : real, (fun y1 : real => ((forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, ((~ ((real_add y1 y2) = y2)) \/ (~ ((real_add y2 y1) = y2))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term132 (x0 : real) := (exists y0 : real, (fun y1 : real => ~ ((real_add x0 y1) = y1)) y0) \/ (exists y0 : real, (fun y1 : real => ~ ((real_add y1 x0) = y1)) y0).
Definition term113 := (exists y0 : real, (fun y1 : real => ((forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) \/ (exists y0 : real, (fun y1 : real => ((exists y2 : real, ~ ((real_add y1 y2) = y2)) \/ (exists y2 : real, ~ ((real_add y2 y1) = y2))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term66 := fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0.
Definition term63 := imp (~ (forall y0 : real, ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) = (y0 = (real_of_num (NUMERAL 0))))).
Definition term51 := imp (~ (forall y0 : real, ((fun y1 : real => (forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))))).
Definition term50 := imp (~ (forall y0 : real, ((fun y1 : real => forall y2 : real, ((real_add y1 y2) = y2) /\ ((real_add y2 y1) = y2)) y0) = (y0 = (real_of_num (NUMERAL 0))))).
Definition term178 := exists y0 : real, (fun y1 : real => exists y2 : real, ((~ ((real_add y1 y2) = y2)) \/ (~ ((real_add y2 y1) = y2))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0.
Definition term199 (x0 : real) := fun y0 : real => (((forall y1 : real, (real_add x0 y1) = y1) /\ (forall y1 : real, (real_add y1 x0) = y1)) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) \/ ((fun y1 : real => ((~ ((real_add x0 y1) = y1)) \/ (~ ((real_add y1 x0) = y1))) /\ (x0 = (real_of_num (NUMERAL 0)))) y0).
Definition term180 := @eq Prop ((exists y0 : real, ((forall y1 : real, (real_add y0 y1) = y1) /\ (forall y1 : real, (real_add y1 y0) = y1)) /\ (~ (y0 = (real_of_num (NUMERAL 0))))) \/ (exists y0 : real, exists y1 : real, ((~ ((real_add y0 y1) = y1)) \/ (~ ((real_add y1 y0) = y1))) /\ (y0 = (real_of_num (NUMERAL 0))))).
Definition term179 := @eq Prop ((exists y0 : real, (fun y1 : real => ((forall y2 : real, (real_add y1 y2) = y2) /\ (forall y2 : real, (real_add y2 y1) = y2)) /\ (~ (y1 = (real_of_num (NUMERAL 0))))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, ((~ ((real_add y1 y2) = y2)) \/ (~ ((real_add y2 y1) = y2))) /\ (y1 = (real_of_num (NUMERAL 0)))) y0)).
Definition term142 (x0 : real) := @eq Prop ((exists y0 : real, ~ ((real_add x0 y0) = y0)) \/ (exists y0 : real, ~ ((real_add y0 x0) = y0))).
Definition term141 (x0 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => ~ ((real_add x0 y1) = y1)) y0) \/ (exists y0 : real, (fun y1 : real => ~ ((real_add y1 x0) = y1)) y0)).
