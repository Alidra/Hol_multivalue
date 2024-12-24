Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term121 (x0 : real) := ~ ((real_mul (sqrt x0) (sqrt x0)) = x0).
Definition term76 (x0 : real) := ~ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term26 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0.
Definition term10 := forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0).
Definition term65 := exists y0 : real, (~ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) /\ (real_le (real_of_num (NUMERAL 0)) y0).
Definition term141 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))))).
Definition term32 (x0 : real -> Prop) := ~ (all x0).
Definition term149 := (~ False) -> False.
Definition term132 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (real_le x0 x1))))) -> real_le x2 x3.
Definition term58 := fun y0 : real => (fun y1 : real => ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1) /\ (~ (real_le (real_of_num (NUMERAL 0)) y1))) y0.
Definition term110 (x0 : Prop) := ~ (~ x0).
Definition term86 := real_of_num (NUMERAL 0).
Definition term119 (x0 : real) := (((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = (real_mul (sqrt x0) (sqrt x0))) /\ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0)) -> (real_mul (sqrt x0) (sqrt x0)) = x0.
Definition term18 := (~ (forall y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> ~ (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)).
Definition term124 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) (real_mul (sqrt x0) (sqrt x0))).
Definition term118 (x0 : real) := ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = (real_mul (sqrt x0) (sqrt x0))) /\ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term129 (x0 : real) (x1 : real) (x2 : real) := (~ (x2 = x0)) \/ (~ (real_le x1 x2)).
Definition term137 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x2 = x0))) /\ (~ (~ (real_le x1 x2))).
Definition term109 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term138 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term25 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0.
Definition term156 (x0 : real) := imp (real_le (real_of_num (NUMERAL 0)) x0).
Definition term47 := fun y0 : real => (~ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) /\ (real_le (real_of_num (NUMERAL 0)) y0).
Definition term12 := (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> False.
Definition term63 := fun y0 : real => (fun y1 : real => (~ ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1)) /\ (real_le (real_of_num (NUMERAL 0)) y1)) y0.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term153 (x0 : real) := (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))) -> (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term115 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term9 := ~ (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)).
Definition term3 := ~ (forall y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0)).
Definition term24 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term103 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term73 (x0 : real) := (fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) x0.
Definition term29 := fun y0 : real => ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0).
Definition term89 (x0 : Prop) := (~ x0) -> x0.
Definition term53 (x0 : real) := (~ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0)) /\ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term122 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul (sqrt x0) (sqrt x0)).
Definition term69 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0).
Definition term105 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term107 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term75 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term101 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term64 := exists y0 : real, (fun y1 : real => (~ ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1)) /\ (real_le (real_of_num (NUMERAL 0)) y1)) y0.
Definition term59 := exists y0 : real, (fun y1 : real => ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1) /\ (~ (real_le (real_of_num (NUMERAL 0)) y1))) y0.
Definition term102 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term61 := or (exists y0 : real, (fun y1 : real => ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1) /\ (~ (real_le (real_of_num (NUMERAL 0)) y1))) y0).
Definition term39 := exists y0 : real, (((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) /\ (~ (real_le (real_of_num (NUMERAL 0)) y0))) \/ ((~ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) /\ (real_le (real_of_num (NUMERAL 0)) y0)).
Definition term99 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term147 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term157 (x0 : real) := ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0) -> False.
Definition term34 := exists y0 : real, ~ ((fun y1 : real => ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1) = (real_le (real_of_num (NUMERAL 0)) y1)) y0).
Definition term151 (x0 : real) := @eq Prop ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0)).
Definition term146 (x0 : real) := (((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))) /\ (((real_mul (sqrt x0) (sqrt x0)) = x0) /\ (real_le (real_of_num (NUMERAL 0)) (real_mul (sqrt x0) (sqrt x0))))) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term142 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp ((x2 = x0) /\ ((x3 = x1) /\ (real_le x2 x3))).
Definition term85 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term52 (x0 : real) := (fun y0 : real => (~ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) /\ (real_le (real_of_num (NUMERAL 0)) y0)) x0.
Definition term21 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0).
Definition term144 (x0 : real) := ((real_mul (sqrt x0) (sqrt x0)) = x0) /\ (real_le (real_of_num (NUMERAL 0)) (real_mul (sqrt x0) (sqrt x0))).
Definition term83 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) -> (~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))).
Definition term74 (x0 : real) := (fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) x0.
Definition term19 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term96 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term127 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((real_le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term7 := (((~ (forall y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> False) -> (~ (forall y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> False) -> ((~ (forall y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> False) -> (~ (forall y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> False.
Definition term42 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term66 := (exists y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) /\ (~ (real_le (real_of_num (NUMERAL 0)) y0))) \/ (exists y0 : real, (~ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) /\ (real_le (real_of_num (NUMERAL 0)) y0)).
Definition term71 := forall y0 : real, (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term5 := ((~ (forall y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> False) -> (~ (forall y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> False.
Definition term82 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))).
Definition term78 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_le x2 x3) = (real_le x0 x1)) -> (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term131 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((real_le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))))).
Definition term95 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term125 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))).
Definition term13 := (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> ~ (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)).
Definition term43 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term106 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term87 := (~ ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0)))) -> (real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0)).
Definition term6 := (((~ (forall y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> False) -> (~ (forall y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> False) -> (~ (forall y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> False.
Definition term38 := fun y0 : real => (((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) /\ (~ (real_le (real_of_num (NUMERAL 0)) y0))) \/ ((~ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) /\ (real_le (real_of_num (NUMERAL 0)) y0)).
Definition term145 (x0 : real) := ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))) /\ (((real_mul (sqrt x0) (sqrt x0)) = x0) /\ (real_le (real_of_num (NUMERAL 0)) (real_mul (sqrt x0) (sqrt x0)))).
Definition term92 (x0 : real) := ~ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = (real_mul (sqrt x0) (sqrt x0))).
Definition term57 := @eq Prop (exists y0 : real, (((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) /\ (~ (real_le (real_of_num (NUMERAL 0)) y0))) \/ ((~ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) /\ (real_le (real_of_num (NUMERAL 0)) y0))).
Definition term56 := @eq Prop (exists y0 : real, ((fun y1 : real => ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1) /\ (~ (real_le (real_of_num (NUMERAL 0)) y1))) y0) \/ ((fun y1 : real => (~ ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1)) /\ (real_le (real_of_num (NUMERAL 0)) y1)) y0)).
Definition term148 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) -> False.
Definition term70 := fun y0 : real => (~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term33 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term8 := (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> False.
Definition term22 := fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0).
Definition term134 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term28 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term2 := (~ (forall y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0))) -> False.
Definition term143 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((x0 = x2) /\ ((x1 = x3) /\ (real_le x0 x1))) -> real_le x2 x3.
Definition term31 (x0 : real) := (((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) x0))) \/ ((~ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0)) /\ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term114 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term72 (x0 : real) := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) x0.
Definition term4 := (~ (forall y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0))) -> (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> False.
Definition term100 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term98 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term91 (x0 : real) := (~ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = (real_mul (sqrt x0) (sqrt x0)))) -> (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = (real_mul (sqrt x0) (sqrt x0)).
Definition term35 (x0 : real) := (fun y0 : real => ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0)) x0.
Definition term128 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term139 (x0 : real) (x1 : real) (x2 : real) := (x2 = x0) /\ (real_le x1 x2).
Definition term112 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term49 (x0 : real) := ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term20 := fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0).
Definition term55 := fun y0 : real => ((fun y1 : real => ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1) /\ (~ (real_le (real_of_num (NUMERAL 0)) y1))) y0) \/ ((fun y1 : real => (~ ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1)) /\ (real_le (real_of_num (NUMERAL 0)) y1)) y0).
Definition term77 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term120 (x0 : real) := (~ ((real_mul (sqrt x0) (sqrt x0)) = x0)) -> (real_mul (sqrt x0) (sqrt x0)) = x0.
Definition term93 (x0 : real) := (~ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0)) -> (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0.
Definition term44 := exists y0 : real, ((fun y1 : real => ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1) /\ (~ (real_le (real_of_num (NUMERAL 0)) y1))) y0) \/ ((fun y1 : real => (~ ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1)) /\ (real_le (real_of_num (NUMERAL 0)) y1)) y0).
Definition term16 := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> ~ (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)).
Definition term51 (x0 : real) := or (((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term54 (x0 : real) := ((fun y0 : real => ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) /\ (~ (real_le (real_of_num (NUMERAL 0)) y0))) x0) \/ ((fun y0 : real => (~ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) /\ (real_le (real_of_num (NUMERAL 0)) y0)) x0).
Definition term27 (x0 : real) := real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term123 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) (real_mul (sqrt x0) (sqrt x0)))) -> real_le (real_of_num (NUMERAL 0)) (real_mul (sqrt x0) (sqrt x0)).
Definition term1 := forall y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0).
Definition term126 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term150 (x0 : real) := ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0) \/ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term60 := exists y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) /\ (~ (real_le (real_of_num (NUMERAL 0)) y0)).
Definition term133 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))).
Definition term117 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term136 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x2 = x0)) \/ (~ (real_le x1 x2))).
Definition term108 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term104 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term130 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))))).
Definition term152 (x0 : real) := @eq Prop (((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0) \/ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term113 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term90 (x0 : real) := real_mul (sqrt x0) (sqrt x0).
Definition term81 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term135 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term48 (x0 : real) := (fun y0 : real => ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) /\ (~ (real_le (real_of_num (NUMERAL 0)) y0))) x0.
Definition term14 := imp (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term11 := imp (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)).
Definition term36 (x0 : real) := ~ ((fun y0 : real => ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0)) x0).
Definition term37 := fun y0 : real => ~ ((fun y1 : real => ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1) = (real_le (real_of_num (NUMERAL 0)) y1)) y0).
Definition term80 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x3 = x1) -> (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term140 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) /\ ((x3 = x1) /\ (real_le x2 x3)).
Definition term116 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term50 (x0 : real) := or ((fun y0 : real => ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) /\ (~ (real_le (real_of_num (NUMERAL 0)) y0))) x0).
Definition term94 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term111 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term23 := forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0).
Definition term97 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term62 := or (exists y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) /\ (~ (real_le (real_of_num (NUMERAL 0)) y0))).
Definition term154 (x0 : real) := ~ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term15 := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) -> (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) -> (forall y0 : real, (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) -> False.
Definition term84 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3)))).
Definition term30 (x0 : real) := ~ (((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = x0) = (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term45 := (exists y0 : real, (fun y1 : real => ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1) /\ (~ (real_le (real_of_num (NUMERAL 0)) y1))) y0) \/ (exists y0 : real, (fun y1 : real => (~ ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1)) /\ (real_le (real_of_num (NUMERAL 0)) y1)) y0).
Definition term17 := imp (~ (forall y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) = (real_le (real_of_num (NUMERAL 0)) y0))).
Definition term155 (x0 : real) := imp (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term88 := ~ ((real_of_num (NUMERAL 0)) = (real_of_num (NUMERAL 0))).
Definition term79 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term68 := @eq Prop ((exists y0 : real, ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) /\ (~ (real_le (real_of_num (NUMERAL 0)) y0))) \/ (exists y0 : real, (~ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0)) /\ (real_le (real_of_num (NUMERAL 0)) y0))).
Definition term67 := @eq Prop ((exists y0 : real, (fun y1 : real => ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1) /\ (~ (real_le (real_of_num (NUMERAL 0)) y1))) y0) \/ (exists y0 : real, (fun y1 : real => (~ ((real_pow (sqrt y1) (NUMERAL (BIT0 (BIT1 0)))) = y1)) /\ (real_le (real_of_num (NUMERAL 0)) y1)) y0)).
Definition term46 := fun y0 : real => ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = y0) /\ (~ (real_le (real_of_num (NUMERAL 0)) y0)).
