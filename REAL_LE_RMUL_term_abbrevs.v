Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term101 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> real_le x0 x1.
Definition term147 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))))).
Definition term43 (x0 : real -> Prop) := ~ (all x0).
Definition term155 := (~ False) -> False.
Definition term85 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ ((~ (real_le x0 x2)) \/ (real_le (real_mul x1 x0) (real_mul x1 x2))).
Definition term18 := imp (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)).
Definition term136 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (real_le x0 x1))))) -> real_le x2 x3.
Definition term69 (x0 : real) (x1 : real) (x2 : real) := or (~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x1 x2))).
Definition term88 (x0 : real) (x1 : real) (x2 : real) := ~ (real_le (real_mul x0 x2) (real_mul x1 x2)).
Definition term72 (x0 : real) (x1 : real) (x2 : real) := ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_le x0 x2))) \/ (real_le (real_mul x1 x0) (real_mul x1 x2)).
Definition term119 (x0 : Prop) := ~ (~ x0).
Definition term74 (x0 : real) (x1 : real) := fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_le x0 y0))) \/ (real_le (real_mul x1 x0) (real_mul x1 y0)).
Definition term133 (x0 : real) (x1 : real) (x2 : real) := (~ (x2 = x0)) \/ (~ (real_le x1 x2)).
Definition term144 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x2 = x0))) /\ (~ (~ (real_le x1 x2))).
Definition term118 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))) /\ (~ (~ (real_le x1 x2))).
Definition term123 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term109 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((real_le (real_mul x2 x0) (real_mul x2 x1)) \/ ((~ (real_le x0 x1)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x2)))).
Definition term41 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) x2).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term124 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x1 x2)))).
Definition term45 (x0 : real) (x1 : real) := ~ (forall y0 : real, ((real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_mul x0 y0) (real_mul x1 y0)).
Definition term24 (x0 : real) := forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0).
Definition term84 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1.
Definition term113 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term99 (x0 : Prop) := (~ x0) -> x0.
Definition term68 (x0 : real) (x1 : real) (x2 : real) := real_le (real_mul x1 x0) (real_mul x1 x2).
Definition term12 := ((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False.
Definition term33 (x0 : real) (x1 : real) (x2 : real) := ((real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) x2)) -> real_le (real_mul x0 x2) (real_mul x1 x2).
Definition term150 (x0 : real) (x1 : real) (x2 : real) := ((real_mul x1 x2) = (real_mul x2 x1)) /\ (real_le (real_mul x1 x0) (real_mul x1 x2)).
Definition term153 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le (real_mul x0 x2) (real_mul x1 x2))) -> real_le (real_mul x0 x2) (real_mul x1 x2).
Definition term116 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term86 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term79 := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_le y1 y2))) \/ (real_le (real_mul y0 y1) (real_mul y0 y2)).
Definition term77 (x0 : real) := forall y0 : real, forall y1 : real, ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le y0 y1))) \/ (real_le (real_mul x0 y0) (real_mul x0 y1)).
Definition term37 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_mul x0 y1) (real_mul y0 y1).
Definition term32 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2).
Definition term30 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le y0 y1)) -> real_le (real_mul x0 y0) (real_mul x0 y1).
Definition term17 := forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0).
Definition term8 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2).
Definition term64 := exists y0 : real, exists y1 : real, exists y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) /\ (~ (real_le (real_mul y0 y2) (real_mul y1 y2))).
Definition term58 (x0 : real) := exists y0 : real, exists y1 : real, ((real_le x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (~ (real_le (real_mul x0 y1) (real_mul y0 y1))).
Definition term97 (x0 : real) (x1 : real) := (~ ((real_mul x1 x0) = (real_mul x0 x1))) -> (real_mul x1 x0) = (real_mul x0 x1).
Definition term19 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term22 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> ~ (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)).
Definition term100 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term35 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_mul x0 y0) (real_mul x1 y0).
Definition term28 (x0 : real) (x1 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 y0)) -> real_le (real_mul x1 x0) (real_mul x1 y0).
Definition term59 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le (real_of_num (NUMERAL 0)) y3)) -> real_le (real_mul y1 y3) (real_mul y2 y3)) y0).
Definition term53 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, ((real_le x0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul x0 y2) (real_mul y1 y2)) y0).
Definition term46 (x0 : real) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => ((real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_mul x0 y1) (real_mul x1 y1)) y0).
Definition term148 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp ((x2 = x0) /\ ((x3 = x1) /\ (real_le x2 x3))).
Definition term62 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le (real_of_num (NUMERAL 0)) y3)) -> real_le (real_mul y1 y3) (real_mul y2 y3)) y0).
Definition term56 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, ((real_le x0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul x0 y2) (real_mul y1 y2)) y0).
Definition term122 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term57 (x0 : real) := fun y0 : real => exists y1 : real, ((real_le x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (~ (real_le (real_mul x0 y1) (real_mul y0 y1))).
Definition term27 (x0 : real) (x1 : real) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 y0)) -> real_le (real_mul x1 x0) (real_mul x1 y0).
Definition term40 (x0 : real) (x1 : real) (x2 : real) := ((real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) x2)) /\ (~ (real_le (real_mul x0 x2) (real_mul x1 x2))).
Definition term76 (x0 : real) := fun y0 : real => forall y1 : real, ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le y0 y1))) \/ (real_le (real_mul x0 y0) (real_mul x0 y1)).
Definition term36 (x0 : real) := fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_mul x0 y1) (real_mul y0 y1).
Definition term29 (x0 : real) := fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le y0 y1)) -> real_le (real_mul x0 y0) (real_mul x0 y1).
Definition term15 := (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False.
Definition term95 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) -> (~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))).
Definition term129 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term131 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((real_le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term52 (x0 : real) := ~ (forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_mul x0 y1) (real_mul y0 y1)).
Definition term16 := ~ (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)).
Definition term10 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2)).
Definition term127 (x0 : real) (x1 : real) (x2 : real) := ~ (real_le (real_mul x1 x0) (real_mul x1 x2)).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term94 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))).
Definition term90 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_le x2 x3) = (real_le x0 x1)) -> (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term135 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((real_le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))))).
Definition term128 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))).
Definition term102 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x2)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (real_le (real_mul x1 x0) (real_mul x1 x2))).
Definition term115 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term66 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x1 x2)).
Definition term73 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x1 x2).
Definition term61 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2)) x0).
Definition term71 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 x2))) \/ (real_le (real_mul x1 x0) (real_mul x1 x2)).
Definition term108 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ ((~ (real_le x0 x2)) \/ (real_le (real_mul x1 x0) (real_mul x1 x2)))).
Definition term13 := (((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False.
Definition term25 := fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0).
Definition term44 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term48 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => ((real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_mul x0 y0) (real_mul x1 y0)) x2).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term83 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0.
Definition term51 (x0 : real) (x1 : real) := exists y0 : real, ((real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (~ (real_le (real_mul x0 y0) (real_mul x1 y0))).
Definition term138 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term70 (x0 : real) (x1 : real) (x2 : real) := or ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x1 x2))).
Definition term67 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term106 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ ((real_le (real_mul x2 x0) (real_mul x2 x1)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x2))).
Definition term9 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2))) -> False.
Definition term104 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_mul x2 x0) (real_mul x2 x1)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x2)).
Definition term149 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((x0 = x2) /\ ((x1 = x3) /\ (real_le x0 x1))) -> real_le x2 x3.
Definition term114 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_le x0 x2)))) -> real_le (real_mul x1 x0) (real_mul x1 x2).
Definition term14 := (((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False) -> ((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False) -> (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False.
Definition term105 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term132 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term145 (x0 : real) (x1 : real) (x2 : real) := (x2 = x0) /\ (real_le x1 x2).
Definition term121 (x0 : real) := and (~ (~ (real_le (real_of_num (NUMERAL 0)) x0))).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term81 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le y0 y1))) \/ (real_le (real_mul x0 y0) (real_mul x0 y1))) x1.
Definition term54 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_mul x0 y1) (real_mul y0 y1)) x1.
Definition term141 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term50 (x0 : real) (x1 : real) := fun y0 : real => ((real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (~ (real_le (real_mul x0 y0) (real_mul x1 y0))).
Definition term47 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_mul x0 y0) (real_mul x1 y0)) x2.
Definition term42 (x0 : real) (x1 : real) (x2 : real) := real_le (real_mul x0 x2) (real_mul x1 x2).
Definition term89 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term111 (x0 : real) (x1 : real) (x2 : real) := or (real_le (real_mul x1 x0) (real_mul x1 x2)).
Definition term125 (x0 : real) (x1 : real) (x2 : real) := imp ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x1 x2)).
Definition term126 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le (real_mul x1 x0) (real_mul x1 x2))) -> real_le (real_mul x1 x0) (real_mul x1 x2).
Definition term65 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x1 x2)).
Definition term23 (x0 : real) := fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0).
Definition term78 := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_le y1 y2))) \/ (real_le (real_mul y0 y1) (real_mul y0 y2)).
Definition term38 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2).
Definition term31 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2).
Definition term55 (x0 : real) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_mul x0 y1) (real_mul y0 y1)) x1).
Definition term63 := fun y0 : real => exists y1 : real, exists y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) /\ (~ (real_le (real_mul y0 y2) (real_mul y1 y2))).
Definition term82 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_le x0 y0))) \/ (real_le (real_mul x1 x0) (real_mul x1 y0))) x2.
Definition term26 (x0 : real) (x1 : real) (x2 : real) := ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 x2)) -> real_le (real_mul x1 x0) (real_mul x1 x2).
Definition term87 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term137 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))).
Definition term143 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x2 = x0)) \/ (~ (real_le x1 x2))).
Definition term117 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x1 x2))).
Definition term134 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))))).
Definition term34 (x0 : real) (x1 : real) := fun y0 : real => ((real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_mul x0 y0) (real_mul x1 y0).
Definition term152 (x0 : real) (x1 : real) (x2 : real) := (((real_mul x2 x0) = (real_mul x0 x2)) /\ (((real_mul x2 x1) = (real_mul x1 x2)) /\ (real_le (real_mul x2 x0) (real_mul x2 x1)))) -> real_le (real_mul x0 x2) (real_mul x1 x2).
Definition term142 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term20 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> ~ (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)).
Definition term151 (x0 : real) (x1 : real) (x2 : real) := ((real_mul x1 x0) = (real_mul x0 x1)) /\ (((real_mul x1 x2) = (real_mul x2 x1)) /\ (real_le (real_mul x1 x0) (real_mul x1 x2))).
Definition term93 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term139 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term110 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x2)).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term49 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => ((real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_mul x0 y1) (real_mul x1 y1)) y0).
Definition term92 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x3 = x1) -> (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term112 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_mul x0 x1) (real_mul x0 x2)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le x1 x2))).
Definition term107 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_mul x2 x0) (real_mul x2 x1)) \/ ((~ (real_le x0 x1)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x2))).
Definition term39 (x0 : real) (x1 : real) (x2 : real) := ~ (((real_le x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) x2)) -> real_le (real_mul x0 x2) (real_mul x1 x2)).
Definition term146 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) /\ ((x3 = x1) /\ (real_le x2 x3)).
Definition term154 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_mul x0 x2) (real_mul x1 x2)) -> False.
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term75 (x0 : real) (x1 : real) := forall y0 : real, ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (~ (real_le x0 y0))) \/ (real_le (real_mul x1 x0) (real_mul x1 y0)).
Definition term103 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (real_le (real_mul x1 x0) (real_mul x1 x2)).
Definition term98 (x0 : real) (x1 : real) := ~ ((real_mul x1 x0) = (real_mul x0 x1)).
Definition term140 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term130 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term120 (x0 : real) := ~ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term80 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_le y1 y2))) \/ (real_le (real_mul y0 y1) (real_mul y0 y2))) x0.
Definition term60 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2)) x0.
Definition term96 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3)))).
Definition term11 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2)) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) -> False.
Definition term21 := imp (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_mul y0 y2) (real_mul y1 y2))).
Definition term91 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ (~ (real_le x2 x3)).