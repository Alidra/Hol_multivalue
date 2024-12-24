Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term65 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0.
Definition term52 := forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0).
Definition term244 (x0 : real) (x1 : real) := ((sqrt x1) = (sqrt x1)) /\ (real_le (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (sqrt x1)).
Definition term172 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))))).
Definition term74 (x0 : real -> Prop) := ~ (all x0).
Definition term249 := (~ False) -> False.
Definition term26 := (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term30 := imp (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2).
Definition term18 := imp (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)).
Definition term157 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (real_le x0 x1))))) -> real_le x2 x3.
Definition term215 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (real_le x0 x2)) \/ (real_le x1 x2))).
Definition term226 (x0 : real) := ((sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) \/ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term96 (x0 : real) (x1 : real) (x2 : real) := or (~ ((real_le x0 x1) /\ (real_le x1 x2))).
Definition term243 (x0 : real) (x1 : real) := ~ (real_le (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (sqrt x1)).
Definition term163 (x0 : Prop) := ~ (~ x0).
Definition term197 := real_of_num (NUMERAL 0).
Definition term211 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (real_le x2 x0)) \/ (real_le x1 x0))) -> ~ (real_le x1 x2).
Definition term128 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x1 x0)) \/ ((~ (real_le x0 x2)) \/ (real_le x1 x2)).
Definition term237 (x0 : real) (x1 : real) := (~ (~ (real_le x0 x1))) -> real_le (sqrt x0) (sqrt x1).
Definition term42 (x0 : real) (x1 : real) := (real_le x0 x1) -> real_le (sqrt x0) (sqrt x1).
Definition term28 := (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term37 := (~ (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term11 := (~ (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term66 (x0 : real) (x1 : real) := (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1) -> real_le x0 (sqrt x1).
Definition term120 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0)) x2.
Definition term153 (x0 : real) (x1 : real) (x2 : real) := (~ (x2 = x0)) \/ (~ (real_le x1 x2)).
Definition term190 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (real_le x0 x1))) /\ (~ (~ (real_le x1 x2))).
Definition term168 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x2 = x0))) /\ (~ (~ (real_le x1 x2))).
Definition term169 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term111 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) \/ (real_le (sqrt x0) (sqrt x1)).
Definition term40 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_le y0 x0).
Definition term82 (x0 : real) := exists y0 : real, (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) y0) /\ (~ (real_le x0 (sqrt y0))).
Definition term206 (x0 : real) := imp (real_le (real_of_num (NUMERAL 0)) x0).
Definition term179 (x0 : real) (x1 : real) := (~ (real_le (real_mul x0 x0) x1)) -> real_le (real_mul x0 x0) x1.
Definition term109 := fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt y0)).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term193 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2)))).
Definition term76 (x0 : real) := ~ (forall y0 : real, (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) y0) -> real_le x0 (sqrt y0)).
Definition term146 (x0 : real) (x1 : real) := (~ (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1)) -> real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1.
Definition term38 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_le x0 x1).
Definition term47 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term222 (x0 : real) := real_le x0 (real_of_num (NUMERAL 0)).
Definition term79 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) y0) -> real_le x0 (sqrt y0)) x1).
Definition term48 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0).
Definition term156 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term122 (x0 : real) := (fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) x0.
Definition term67 (x0 : real) := fun y0 : real => (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) y0) -> real_le x0 (sqrt y0).
Definition term144 (x0 : real) := (~ (x0 = x0)) -> x0 = x0.
Definition term240 (x0 : real) (x1 : real) := (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1) -> real_le (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (sqrt x1).
Definition term99 (x0 : real) (x1 : real) (x2 : real) := ((~ (real_le x1 x0)) \/ (~ (real_le x0 x2))) \/ (real_le x1 x2).
Definition term141 (x0 : Prop) := (~ x0) -> x0.
Definition term160 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term219 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) (sqrt x0)) /\ (~ (real_le x1 (sqrt x0)))) -> ~ (real_le x1 (real_of_num (NUMERAL 0))).
Definition term199 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term217 (x0 : real) (x1 : real) (x2 : real) := ((real_le x2 x0) /\ (~ (real_le x1 x0))) -> ~ (real_le x1 x2).
Definition term186 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (real_le x1 x0)) \/ ((~ (real_le x0 x2)) \/ (real_le x1 x2))).
Definition term195 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0)) /\ (real_le (real_mul x0 x0) x1).
Definition term116 := forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) \/ (real_le (sqrt y0) (sqrt y1)).
Definition term106 := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2).
Definition term104 (x0 : real) := forall y0 : real, forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1).
Definition term62 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term60 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term46 := forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1).
Definition term17 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term8 := forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1).
Definition term187 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((real_le x0 x2) \/ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2)))).
Definition term88 := exists y0 : real, exists y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) /\ (~ (real_le y0 (sqrt y1))).
Definition term232 (x0 : real) := (~ ((sqrt x0) = (sqrt x0))) -> (sqrt x0) = (sqrt x0).
Definition term71 (x0 : real) (x1 : real) := (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1) /\ (~ (real_le x0 (sqrt x1))).
Definition term19 := (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term64 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0.
Definition term56 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_le x0 x2)) -> real_le x1 x2.
Definition term142 (x0 : real) := (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul x0 x0))) -> (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul x0 x0).
Definition term203 (x0 : real) := (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))) -> real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term25 := (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term198 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term73 (x0 : real) (x1 : real) := real_le x0 (sqrt x1).
Definition term236 (x0 : real) (x1 : real) := @eq Prop ((real_le (sqrt x0) (sqrt x1)) \/ (~ (real_le x0 x1))).
Definition term81 (x0 : real) := fun y0 : real => (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) y0) /\ (~ (real_le x0 (sqrt y0))).
Definition term83 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_le (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) y2) -> real_le y1 (sqrt y2)) y0).
Definition term77 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le x0 (sqrt y1)) y0).
Definition term227 (x0 : real) := @eq Prop ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0)).
Definition term107 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt x0)).
Definition term173 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp ((x2 = x0) /\ ((x3 = x1) /\ (real_le x2 x3))).
Definition term114 (x0 : real) := forall y0 : real, (~ (real_le x0 y0)) \/ (real_le (sqrt x0) (sqrt y0)).
Definition term110 := forall y0 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt y0)).
Definition term200 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) (sqrt x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term248 (x0 : real) (x1 : real) := (real_le x0 (sqrt x1)) -> False.
Definition term86 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_le (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) y2) -> real_le y1 (sqrt y2)) y0).
Definition term207 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) (sqrt x0))) -> real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term53 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0).
Definition term87 := fun y0 : real => exists y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) /\ (~ (real_le y0 (sqrt y1))).
Definition term235 (x0 : real) (x1 : real) := @eq Prop ((~ (real_le x0 x1)) \/ (real_le (sqrt x0) (sqrt x1))).
Definition term212 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (real_le x0 x2)) \/ (real_le x1 x2)).
Definition term115 := fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (real_le (sqrt y0) (sqrt y1)).
Definition term69 := fun y0 : real => forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1).
Definition term45 := fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1).
Definition term15 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term137 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) -> (~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))).
Definition term117 (x0 : real) := (fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0)) x0.
Definition term50 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term149 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term151 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((real_le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term14 := (((~ (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> ((~ (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term16 := ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term10 := ~ (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1)).
Definition term93 := forall y0 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0).
Definition term242 (x0 : real) (x1 : real) := (~ (real_le (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (sqrt x1))) -> real_le (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (sqrt x1).
Definition term108 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term136 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))).
Definition term208 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) (sqrt x0)).
Definition term132 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_le x2 x3) = (real_le x0 x1)) -> (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term155 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((real_le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))))).
Definition term218 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (sqrt x1)) /\ (~ (real_le x0 (sqrt x1))).
Definition term148 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))).
Definition term159 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term98 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_le x1 x0) /\ (real_le x0 x2))) \/ (real_le x1 x2).
Definition term85 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1)) x0).
Definition term241 (x0 : real) (x1 : real) := real_le (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (sqrt x1).
Definition term202 (x0 : real) := @eq Prop ((real_le (real_of_num (NUMERAL 0)) (sqrt x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term125 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_le x0 y0)) \/ (real_le (sqrt x0) (sqrt y0))) x1.
Definition term177 (x0 : real) (x1 : real) := (((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul x0 x0)) /\ ((x1 = x1) /\ (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1))) -> real_le (real_mul x0 x0) x1.
Definition term194 (x0 : real) (x1 : real) (x2 : real) := imp ((real_le x0 x1) /\ (real_le x1 x2)).
Definition term13 := (((~ (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term247 (x0 : real) (x1 : real) := (~ (real_le x0 (sqrt x1))) -> real_le x0 (sqrt x1).
Definition term112 (x0 : real) (x1 : real) := real_le (sqrt x0) (sqrt x1).
Definition term103 (x0 : real) := fun y0 : real => forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1).
Definition term59 (x0 : real) := fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term41 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term43 (x0 : real) := fun y0 : real => (real_le x0 y0) -> real_le (sqrt x0) (sqrt y0).
Definition term91 (x0 : real) := sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term75 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term126 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) x0.
Definition term124 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (real_le (sqrt y0) (sqrt y1))) x0.
Definition term84 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1)) x0.
Definition term54 := fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0).
Definition term12 := ((~ (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term143 (x0 : real) := ~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul x0 x0)).
Definition term161 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term97 (x0 : real) (x1 : real) (x2 : real) := or ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term123 (x0 : real) := (fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt y0))) x0.
Definition term196 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0)) /\ (real_le (real_mul x0 x0) x1)) -> real_le (real_of_num (NUMERAL 0)) x1.
Definition term90 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term70 (x0 : real) (x1 : real) := ~ ((real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1) -> real_le x0 (sqrt x1)).
Definition term9 := (~ (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1))) -> False.
Definition term174 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((x0 = x2) /\ ((x1 = x3) /\ (real_le x0 x1))) -> real_le x2 x3.
Definition term39 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0).
Definition term121 (x0 : real) := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) x0.
Definition term223 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_le x0 x1)).
Definition term230 (x0 : real) := (~ ((sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0)) -> (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0.
Definition term183 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term152 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term170 (x0 : real) (x1 : real) (x2 : real) := (x2 = x0) /\ (real_le x1 x2).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term119 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1)) x1.
Definition term191 (x0 : real) (x1 : real) := and (~ (~ (real_le x0 x1))).
Definition term165 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term188 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x2)))) -> real_le x1 x2.
Definition term147 (x0 : real) (x1 : real) := ~ (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1).
Definition term63 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0.
Definition term51 := fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0).
Definition term101 (x0 : real) (x1 : real) := fun y0 : real => ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0).
Definition term131 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term182 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) \/ (~ (real_le x1 x2)).
Definition term214 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) /\ (~ (real_le x1 x2)).
Definition term140 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0)).
Definition term23 := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term209 (x0 : real) (x1 : real) := (real_le x0 (sqrt x1)) -> ~ (real_le x0 (sqrt x1)).
Definition term105 := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2).
Definition term61 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term49 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0).
Definition term44 (x0 : real) := forall y0 : real, (real_le x0 y0) -> real_le (sqrt x0) (sqrt y0).
Definition term78 (x0 : real) (x1 : real) := (fun y0 : real => (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) y0) -> real_le x0 (sqrt y0)) x1.
Definition term239 (x0 : real) (x1 : real) := imp (real_le x0 x1).
Definition term129 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term32 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term31 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term158 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))).
Definition term231 (x0 : real) := ~ ((sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0).
Definition term189 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term167 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x2 = x0)) \/ (~ (real_le x1 x2))).
Definition term178 (x0 : real) (x1 : real) := real_le (real_mul x0 x0) x1.
Definition term58 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term154 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))))).
Definition term228 (x0 : real) := @eq Prop (((sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) \/ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term166 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term176 (x0 : real) (x1 : real) := ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul x0 x0)) /\ ((x1 = x1) /\ (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1)).
Definition term20 := (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term192 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term135 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term145 (x0 : real) := ~ (x0 = x0).
Definition term162 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term100 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le x1 x2).
Definition term229 (x0 : real) := (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))) -> (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0.
Definition term201 (x0 : real) := @eq Prop ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (real_le (real_of_num (NUMERAL 0)) (sqrt x0))).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term33 := imp (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0).
Definition term27 := imp (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)).
Definition term24 := imp (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)).
Definition term21 := imp (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)).
Definition term130 (x0 : real) (x1 : real) := ~ (real_le x0 (sqrt x1)).
Definition term175 (x0 : real) (x1 : real) := (x1 = x1) /\ (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1).
Definition term80 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le x0 (sqrt y1)) y0).
Definition term134 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x3 = x1) -> (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term246 (x0 : real) (x1 : real) := (((sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) /\ (((sqrt x1) = (sqrt x1)) /\ (real_le (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (sqrt x1)))) -> real_le x0 (sqrt x1).
Definition term68 (x0 : real) := forall y0 : real, (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) y0) -> real_le x0 (sqrt y0).
Definition term113 (x0 : real) := fun y0 : real => (~ (real_le x0 y0)) \/ (real_le (sqrt x0) (sqrt y0)).
Definition term245 (x0 : real) (x1 : real) := ((sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0) /\ (((sqrt x1) = (sqrt x1)) /\ (real_le (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (sqrt x1))).
Definition term171 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) /\ ((x3 = x1) /\ (real_le x2 x3)).
Definition term225 (x0 : real) := (~ (real_le x0 (real_of_num (NUMERAL 0)))) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term57 (x0 : real) (x1 : real) := fun y0 : real => ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term184 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ ((real_le x0 x2) \/ (~ (real_le x1 x2))).
Definition term92 := fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0).
Definition term164 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term55 := forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0).
Definition term150 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term94 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_le x0 x1) /\ (real_le x1 x2)).
Definition term72 (x0 : real) (x1 : real) := real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1.
Definition term181 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x2)) \/ (real_le x1 x2).
Definition term220 (x0 : real) := ~ (real_le x0 (real_of_num (NUMERAL 0))).
Definition term204 (x0 : real) := ~ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term118 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2)) x0.
Definition term89 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = x0).
Definition term22 := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term138 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3)))).
Definition term35 := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term34 := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term139 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0))) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0).
Definition term180 (x0 : real) (x1 : real) := ~ (real_le (real_mul x0 x0) x1).
Definition term221 (x0 : real) := (real_le x0 (real_of_num (NUMERAL 0))) -> ~ (real_le x0 (real_of_num (NUMERAL 0))).
Definition term233 (x0 : real) := ~ ((sqrt x0) = (sqrt x0)).
Definition term185 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) \/ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term224 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) -> real_le x0 x1.
Definition term127 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0)) x1.
Definition term36 := imp (~ (forall y0 : real, forall y1 : real, (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_le y0 (sqrt y1))).
Definition term205 (x0 : real) := imp (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term210 (x0 : Prop) := x0 -> ~ x0.
Definition term234 (x0 : real) (x1 : real) := (real_le (sqrt x0) (sqrt x1)) \/ (~ (real_le x0 x1)).
Definition term216 (x0 : real) (x1 : real) (x2 : real) := imp ((real_le x0 x2) /\ (~ (real_le x1 x2))).
Definition term133 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term102 (x0 : real) (x1 : real) := forall y0 : real, ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0).
Definition term29 := (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (sqrt y0)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (sqrt y0) (sqrt y1)) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term95 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ (~ (real_le x1 x2)).
Definition term213 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (real_le x0 x2))) /\ (~ (real_le x1 x2)).
Definition term238 (x0 : real) (x1 : real) := imp (~ (~ (real_le x0 x1))).
