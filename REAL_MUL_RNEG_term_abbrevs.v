Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term82 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (~ ((real_add x0 y0) = (real_add x1 y0))) \/ (x0 = x1)) x2.
Definition term47 (x0 : real -> Prop) := ~ (all x0).
Definition term283 := (~ False) -> False.
Definition term205 (x0 : real) := (~ ((real_add (real_neg x0) x0) = (real_of_num (NUMERAL 0)))) -> (real_add (real_neg x0) x0) = (real_of_num (NUMERAL 0)).
Definition term19 := (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> ~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)).
Definition term11 := imp (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))).
Definition term99 (x0 : real -> Prop) (x1 : Prop) := forall y0 : real, (x0 y0) \/ x1.
Definition term135 (x0 : real) (x1 : real) := (forall y0 : real, ~ ((real_add x0 y0) = (real_add x1 y0))) \/ (x0 = x1).
Definition term120 (x0 : real) (x1 : real) := (forall y0 : real, (fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0) \/ (x0 = x1).
Definition term56 (x0 : real) := exists y0 : real, ~ ((real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0))).
Definition term23 (x0 : real) (x1 : real) := forall y0 : real, ((real_add x0 y0) = (real_add x1 y0)) = (x0 = x1).
Definition term266 (x0 : real) (x1 : real) := (~ ((real_of_num (NUMERAL 0)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)))) -> (real_of_num (NUMERAL 0)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)).
Definition term221 (x0 : Prop) := ~ (~ x0).
Definition term36 := real_of_num (NUMERAL 0).
Definition term281 (x0 : real) (x1 : real) := (~ ((real_mul x0 (real_neg x1)) = (real_neg (real_mul x0 x1)))) -> (real_mul x0 (real_neg x1)) = (real_neg (real_mul x0 x1)).
Definition term176 := and (forall y0 : real, forall y1 : real, (forall y2 : real, (real_add y0 y2) = (real_add y1 y2)) \/ (~ (y0 = y1))).
Definition term4 := (~ (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) -> False.
Definition term51 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0))) x1.
Definition term261 (x0 : real) (x1 : real) := ~ ((real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)) = (real_of_num (NUMERAL 0))).
Definition term229 (x0 : real) (x1 : real) := (x0 = x0) /\ ((real_add (real_neg x1) x1) = (real_of_num (NUMERAL 0))).
Definition term108 (x0 : real) (x1 : real) (x2 : real) := ((fun y0 : real => (real_add x1 y0) = (real_add x2 y0)) x0) \/ (~ (x1 = x2)).
Definition term220 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x0 = x1))) /\ (~ (~ (x2 = x3))).
Definition term154 (x0 : real) := and (forall y0 : real, (forall y1 : real, (real_add x0 y1) = (real_add y0 y1)) \/ (~ (x0 = y0))).
Definition term92 (x0 : real) (x1 : real) := and (forall y0 : real, ((real_add x0 y0) = (real_add x1 y0)) \/ (~ (x0 = x1))).
Definition term246 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term213 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop (((real_mul x0 x2) = (real_mul x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term166 (x0 : real) := and ((fun y0 : real => forall y1 : real, (forall y2 : real, (real_add y0 y2) = (real_add y1 y2)) \/ (~ (y0 = y1))) x0).
Definition term38 := forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0)).
Definition term78 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_add x0 y0) = (real_add x1 y0)) \/ (~ (x0 = x1))) x2.
Definition term175 := and (forall y0 : real, (fun y1 : real => forall y2 : real, (forall y3 : real, (real_add y1 y3) = (real_add y2 y3)) \/ (~ (y1 = y2))) y0).
Definition term153 (x0 : real) := and (forall y0 : real, (fun y1 : real => (forall y2 : real, (real_add x0 y2) = (real_add y1 y2)) \/ (~ (x0 = y1))) y0).
Definition term91 (x0 : real) (x1 : real) := and (forall y0 : real, (fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) \/ (~ (x0 = x1))) y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term248 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term226 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term49 (x0 : real) := ~ (forall y0 : real, (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0))).
Definition term130 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0.
Definition term95 (x0 : real) (x1 : real) := forall y0 : real, (~ ((real_add x0 y0) = (real_add x1 y0))) \/ (x0 = x1).
Definition term236 (x0 : real) (x1 : real) := ~ ((real_mul x0 (real_add (real_neg x1) x1)) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1))).
Definition term159 := fun y0 : real => (forall y1 : real, (forall y2 : real, (real_add y0 y2) = (real_add y1 y2)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (forall y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) \/ (y0 = y1)).
Definition term231 (x0 : real) (x1 : real) := real_mul x0 (real_add (real_neg x1) x1).
Definition term251 (x0 : real) (x1 : real) := ((real_mul x0 (real_add (real_neg x1) x1)) = (real_mul x0 (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 (real_add (real_neg x1) x1)) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1))).
Definition term257 (x0 : real) (x1 : real) := (~ ((real_of_num (NUMERAL 0)) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1)))) -> (real_of_num (NUMERAL 0)) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1)).
Definition term267 (x0 : real) (x1 : real) := ~ ((real_of_num (NUMERAL 0)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1))).
Definition term103 (x0 : real) (x1 : real) := fun y0 : real => (real_add x0 y0) = (real_add x1 y0).
Definition term180 := (forall y0 : real, forall y1 : real, (forall y2 : real, (real_add y0 y2) = (real_add y1 y2)) \/ (~ (y0 = y1))) /\ (forall y0 : real, forall y1 : real, (forall y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) \/ (y0 = y1)).
Definition term200 (x0 : real) := (~ ((real_mul x0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)))) -> (real_mul x0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)).
Definition term52 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0))) x1).
Definition term214 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term117 (x0 : real) (x1 : real) := (forall y0 : real, (real_add x0 y0) = (real_add x1 y0)) \/ (~ (x0 = x1)).
Definition term162 := (forall y0 : real, (fun y1 : real => forall y2 : real, (forall y3 : real, (real_add y1 y3) = (real_add y2 y3)) \/ (~ (y1 = y2))) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, (forall y3 : real, ~ ((real_add y1 y3) = (real_add y2 y3))) \/ (y1 = y2)) y0).
Definition term140 (x0 : real) := (forall y0 : real, (fun y1 : real => (forall y2 : real, (real_add x0 y2) = (real_add y1 y2)) \/ (~ (x0 = y1))) y0) /\ (forall y0 : real, (fun y1 : real => (forall y2 : real, ~ ((real_add x0 y2) = (real_add y1 y2))) \/ (x0 = y1)) y0).
Definition term75 (x0 : real) (x1 : real) := (forall y0 : real, (fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) \/ (~ (x0 = x1))) y0) /\ (forall y0 : real, (fun y1 : real => (~ ((real_add x0 y1) = (real_add x1 y1))) \/ (x0 = x1)) y0).
Definition term272 (x0 : real) (x1 : real) (x2 : real) := (x0 = x1) \/ (~ ((real_add x0 x2) = (real_add x1 x2))).
Definition term53 (x0 : real) (x1 : real) := ~ ((real_mul x0 (real_neg x1)) = (real_neg (real_mul x0 x1))).
Definition term203 (x0 : real) := (~ (x0 = x0)) -> x0 = x0.
Definition term42 (x0 : real) (x1 : real) := real_mul x0 (real_neg x1).
Definition term114 (x0 : real) (x1 : real) := forall y0 : real, (real_add x0 y0) = (real_add x1 y0).
Definition term202 (x0 : Prop) := (~ x0) -> x0.
Definition term227 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp ((x0 = x1) /\ (x2 = x3)).
Definition term145 (x0 : real) (x1 : real) := (fun y0 : real => (forall y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) \/ (x0 = y0)) x1.
Definition term142 (x0 : real) := fun y0 : real => (forall y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) \/ (x0 = y0).
Definition term119 (x0 : real) (x1 : real) := forall y0 : real, ((fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0) \/ (x0 = x1).
Definition term259 (x0 : real) (x1 : real) := real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1).
Definition term244 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term177 := fun y0 : real => (fun y1 : real => forall y2 : real, (forall y3 : real, ~ ((real_add y1 y3) = (real_add y2 y3))) \/ (y1 = y2)) y0.
Definition term172 := fun y0 : real => (fun y1 : real => forall y2 : real, (forall y3 : real, (real_add y1 y3) = (real_add y2 y3)) \/ (~ (y1 = y2))) y0.
Definition term157 (x0 : real) := forall y0 : real, (forall y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) \/ (x0 = y0).
Definition term218 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term118 (x0 : real) (x1 : real) := and ((forall y0 : real, (real_add x0 y0) = (real_add x1 y0)) \/ (~ (x0 = x1))).
Definition term255 (x0 : real) (x1 : real) := ((real_mul x0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) /\ ((real_mul x0 (real_of_num (NUMERAL 0))) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1))).
Definition term197 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x0 = x2) -> (~ (x1 = x3)) \/ ((real_mul x0 x1) = (real_mul x2 x3)).
Definition term241 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term228 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((x0 = x2) /\ (x1 = x3)) -> (real_mul x0 x1) = (real_mul x2 x3).
Definition term44 (x0 : real) := fun y0 : real => (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0)).
Definition term201 (x0 : real) := ~ ((real_mul x0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term186 := forall y0 : real, forall y1 : real, forall y2 : real, (~ ((real_add y0 y2) = (real_add y1 y2))) \/ (y0 = y1).
Definition term184 (x0 : real) := forall y0 : real, forall y1 : real, (~ ((real_add x0 y1) = (real_add y0 y1))) \/ (x0 = y0).
Definition term179 := forall y0 : real, forall y1 : real, (forall y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) \/ (y0 = y1).
Definition term174 := forall y0 : real, forall y1 : real, (forall y2 : real, (real_add y0 y2) = (real_add y1 y2)) \/ (~ (y0 = y1)).
Definition term69 := forall y0 : real, forall y1 : real, forall y2 : real, (((real_add y0 y2) = (real_add y1 y2)) \/ (~ (y0 = y1))) /\ ((~ ((real_add y0 y2) = (real_add y1 y2))) \/ (y0 = y1)).
Definition term67 (x0 : real) := forall y0 : real, forall y1 : real, (((real_add x0 y1) = (real_add y0 y1)) \/ (~ (x0 = y0))) /\ ((~ ((real_add x0 y1) = (real_add y0 y1))) \/ (x0 = y0)).
Definition term34 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2)).
Definition term32 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul x0 (real_add y0 y1)) = (real_add (real_mul x0 y0) (real_mul x0 y1)).
Definition term25 (x0 : real) := forall y0 : real, forall y1 : real, ((real_add x0 y1) = (real_add y0 y1)) = (x0 = y0).
Definition term10 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1).
Definition term1 := forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)).
Definition term235 (x0 : real) (x1 : real) := (~ ((real_mul x0 (real_add (real_neg x1) x1)) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1)))) -> (real_mul x0 (real_add (real_neg x1) x1)) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1)).
Definition term242 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term138 (x0 : real) := forall y0 : real, ((forall y1 : real, (real_add x0 y1) = (real_add y0 y1)) \/ (~ (x0 = y0))) /\ ((forall y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) \/ (x0 = y0)).
Definition term65 (x0 : real) (x1 : real) := forall y0 : real, (((real_add x0 y0) = (real_add x1 y0)) \/ (~ (x0 = x1))) /\ ((~ ((real_add x0 y0) = (real_add x1 y0))) \/ (x0 = x1)).
Definition term106 (x0 : real) (x1 : real) (x2 : real) := or ((fun y0 : real => (real_add x0 y0) = (real_add x1 y0)) x2).
Definition term62 := exists y0 : real, exists y1 : real, ~ ((real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))).
Definition term125 (x0 : real) (x1 : real) (x2 : real) := or (~ ((real_add x0 x2) = (real_add x1 x2))).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term12 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) -> False.
Definition term116 (x0 : real) (x1 : real) := or (forall y0 : real, (real_add x0 y0) = (real_add x1 y0)).
Definition term98 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) \/ x1.
Definition term79 (x0 : real) (x1 : real) (x2 : real) := ((real_add x1 x0) = (real_add x2 x0)) \/ (~ (x1 = x2)).
Definition term210 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term18 := (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) -> False.
Definition term211 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_mul x0 x2) = (real_mul x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term43 (x0 : real) (x1 : real) := real_neg (real_mul x0 x1).
Definition term57 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_mul y1 (real_neg y2)) = (real_neg (real_mul y1 y2))) y0).
Definition term50 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_mul x0 (real_neg y1)) = (real_neg (real_mul x0 y1))) y0).
Definition term122 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ~ ((real_add x0 y0) = (real_add x1 y0))) x2.
Definition term30 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x1 (real_add x0 y0)) = (real_add (real_mul x1 x0) (real_mul x1 y0)).
Definition term215 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (real_mul x0 x1) = (real_mul x2 x3).
Definition term60 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_mul y1 (real_neg y2)) = (real_neg (real_mul y1 y2))) y0).
Definition term171 := @eq Prop (forall y0 : real, (forall y1 : real, (forall y2 : real, (real_add y0 y2) = (real_add y1 y2)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (forall y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) \/ (y0 = y1))).
Definition term170 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, (forall y3 : real, (real_add y1 y3) = (real_add y2 y3)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, (forall y3 : real, ~ ((real_add y1 y3) = (real_add y2 y3))) \/ (y1 = y2)) y0)).
Definition term149 (x0 : real) := @eq Prop (forall y0 : real, ((forall y1 : real, (real_add x0 y1) = (real_add y0 y1)) \/ (~ (x0 = y0))) /\ ((forall y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) \/ (x0 = y0))).
Definition term148 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (forall y2 : real, (real_add x0 y2) = (real_add y1 y2)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => (forall y2 : real, ~ ((real_add x0 y2) = (real_add y1 y2))) \/ (x0 = y1)) y0)).
Definition term129 (x0 : real) (x1 : real) := @eq Prop (forall y0 : real, (~ ((real_add x0 y0) = (real_add x1 y0))) \/ (x0 = x1)).
Definition term128 (x0 : real) (x1 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0) \/ (x0 = x1)).
Definition term111 (x0 : real) (x1 : real) := @eq Prop (forall y0 : real, ((real_add x0 y0) = (real_add x1 y0)) \/ (~ (x0 = x1))).
Definition term110 (x0 : real) (x1 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => (real_add x0 y1) = (real_add x1 y1)) y0) \/ (~ (x0 = x1))).
Definition term87 (x0 : real) (x1 : real) := @eq Prop (forall y0 : real, (((real_add x0 y0) = (real_add x1 y0)) \/ (~ (x0 = x1))) /\ ((~ ((real_add x0 y0) = (real_add x1 y0))) \/ (x0 = x1))).
Definition term86 (x0 : real) (x1 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) \/ (~ (x0 = x1))) y0) /\ ((fun y1 : real => (~ ((real_add x0 y1) = (real_add x1 y1))) \/ (x0 = x1)) y0)).
Definition term199 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term253 (x0 : real) (x1 : real) := (~ ((real_mul x0 (real_of_num (NUMERAL 0))) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1)))) -> (real_mul x0 (real_of_num (NUMERAL 0))) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1)).
Definition term230 (x0 : real) (x1 : real) := ((x1 = x1) /\ ((real_add (real_neg x0) x0) = (real_of_num (NUMERAL 0)))) -> (real_mul x1 (real_add (real_neg x0) x0)) = (real_mul x1 (real_of_num (NUMERAL 0))).
Definition term260 (x0 : real) (x1 : real) := (~ ((real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)) = (real_of_num (NUMERAL 0)))) -> (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)) = (real_of_num (NUMERAL 0)).
Definition term66 (x0 : real) := fun y0 : real => forall y1 : real, (((real_add x0 y1) = (real_add y0 y1)) \/ (~ (x0 = y0))) /\ ((~ ((real_add x0 y1) = (real_add y0 y1))) \/ (x0 = y0)).
Definition term31 (x0 : real) := fun y0 : real => forall y1 : real, (real_mul x0 (real_add y0 y1)) = (real_add (real_mul x0 y0) (real_mul x0 y1)).
Definition term234 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1).
Definition term8 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) -> False.
Definition term22 (x0 : real) (x1 : real) := fun y0 : real => ((real_add x0 y0) = (real_add x1 y0)) = (x0 = x1).
Definition term104 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term7 := (((~ (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) -> False) -> ((~ (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) -> False.
Definition term35 (x0 : real) := real_add (real_neg x0) x0.
Definition term9 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)).
Definition term3 := ~ (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))).
Definition term81 (x0 : real) (x1 : real) (x2 : real) := and (((real_add x1 x0) = (real_add x2 x0)) \/ (~ (x1 = x2))).
Definition term277 (x0 : real) (x1 : real) (x2 : real) := imp (~ (~ ((real_add x0 x2) = (real_add x1 x2)))).
Definition term187 (x0 : real) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) x0.
Definition term238 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term258 (x0 : real) (x1 : real) := ~ ((real_of_num (NUMERAL 0)) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1))).
Definition term134 (x0 : real) (x1 : real) := or (forall y0 : real, ~ ((real_add x0 y0) = (real_add x1 y0))).
Definition term217 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term158 (x0 : real) := (forall y0 : real, (forall y1 : real, (real_add x0 y1) = (real_add y0 y1)) \/ (~ (x0 = y0))) /\ (forall y0 : real, (forall y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) \/ (x0 = y0)).
Definition term96 (x0 : real) (x1 : real) := (forall y0 : real, ((real_add x0 y0) = (real_add x1 y0)) \/ (~ (x0 = x1))) /\ (forall y0 : real, (~ ((real_add x0 y0) = (real_add x1 y0))) \/ (x0 = x1)).
Definition term280 (x0 : real) (x1 : real) := ((real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1))) -> (real_mul x0 (real_neg x1)) = (real_neg (real_mul x0 x1)).
Definition term127 (x0 : real) (x1 : real) := fun y0 : real => ((fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0) \/ (x0 = x1).
Definition term279 (x0 : real) (x1 : real) (x2 : real) := ((real_add x1 x0) = (real_add x2 x0)) -> x1 = x2.
Definition term100 (x0 : real -> Prop) (x1 : Prop) := (forall y0 : real, x0 y0) \/ x1.
Definition term59 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) x0).
Definition term133 (x0 : real) (x1 : real) := or (forall y0 : real, (fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0).
Definition term115 (x0 : real) (x1 : real) := or (forall y0 : real, (fun y1 : real => (real_add x0 y1) = (real_add x1 y1)) y0).
Definition term101 (x0 : real) (x1 : real) := forall y0 : real, ((fun y1 : real => (real_add x0 y1) = (real_add x1 y1)) y0) \/ (~ (x0 = x1)).
Definition term212 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((real_mul x0 x1) = (real_mul x2 x3)))).
Definition term45 (x0 : real) := forall y0 : real, (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0)).
Definition term150 (x0 : real) := fun y0 : real => (fun y1 : real => (forall y2 : real, (real_add x0 y2) = (real_add y1 y2)) \/ (~ (x0 = y1))) y0.
Definition term88 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) \/ (~ (x0 = x1))) y0.
Definition term274 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x1) \/ (~ ((real_add x0 x2) = (real_add x1 x2)))).
Definition term6 := (((~ (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) -> False.
Definition term83 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add x1 x0) = (real_add x2 x0))) \/ (x1 = x2).
Definition term37 := fun y0 : real => (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0)).
Definition term232 (x0 : real) (x1 : real) := (~ ((real_mul x1 (real_add (real_neg x0) x0)) = (real_mul x1 (real_of_num (NUMERAL 0))))) -> (real_mul x1 (real_add (real_neg x0) x0)) = (real_mul x1 (real_of_num (NUMERAL 0))).
Definition term183 (x0 : real) := fun y0 : real => forall y1 : real, (~ ((real_add x0 y1) = (real_add y0 y1))) \/ (x0 = y0).
Definition term164 := fun y0 : real => forall y1 : real, (forall y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) \/ (y0 = y1).
Definition term24 (x0 : real) := fun y0 : real => forall y1 : real, ((real_add x0 y1) = (real_add y0 y1)) = (x0 = y0).
Definition term48 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term72 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term194 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x1 = x3) -> (real_mul x0 x1) = (real_mul x2 x3).
Definition term167 (x0 : real) := (fun y0 : real => forall y1 : real, (forall y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) \/ (y0 = y1)) x0.
Definition term165 (x0 : real) := (fun y0 : real => forall y1 : real, (forall y2 : real, (real_add y0 y2) = (real_add y1 y2)) \/ (~ (y0 = y1))) x0.
Definition term58 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) x0.
Definition term152 (x0 : real) := forall y0 : real, (forall y1 : real, (real_add x0 y1) = (real_add y0 y1)) \/ (~ (x0 = y0)).
Definition term196 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x1 = x3)) \/ ((real_mul x0 x1) = (real_mul x2 x3)).
Definition term5 := ((~ (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) -> False) -> (~ (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) -> False.
Definition term131 (x0 : real) (x1 : real) := forall y0 : real, (fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0.
Definition term126 (x0 : real) (x1 : real) (x2 : real) := ((fun y0 : real => ~ ((real_add x1 y0) = (real_add x2 y0))) x0) \/ (x1 = x2).
Definition term2 := (~ (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)))) -> False.
Definition term256 (x0 : real) (x1 : real) := (((real_mul x0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) /\ ((real_mul x0 (real_of_num (NUMERAL 0))) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1)))) -> (real_of_num (NUMERAL 0)) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1)).
Definition term156 (x0 : real) := forall y0 : real, (fun y1 : real => (forall y2 : real, ~ ((real_add x0 y2) = (real_add y1 y2))) \/ (x0 = y1)) y0.
Definition term151 (x0 : real) := forall y0 : real, (fun y1 : real => (forall y2 : real, (real_add x0 y2) = (real_add y1 y2)) \/ (~ (x0 = y1))) y0.
Definition term113 (x0 : real) (x1 : real) := forall y0 : real, (fun y1 : real => (real_add x0 y1) = (real_add x1 y1)) y0.
Definition term94 (x0 : real) (x1 : real) := forall y0 : real, (fun y1 : real => (~ ((real_add x0 y1) = (real_add x1 y1))) \/ (x0 = x1)) y0.
Definition term89 (x0 : real) (x1 : real) := forall y0 : real, (fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) \/ (~ (x0 = x1))) y0.
Definition term247 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term28 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul x1 x0) (real_mul x1 x2).
Definition term169 := fun y0 : real => ((fun y1 : real => forall y2 : real, (forall y3 : real, (real_add y1 y3) = (real_add y2 y3)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, (forall y3 : real, ~ ((real_add y1 y3) = (real_add y2 y3))) \/ (y1 = y2)) y0).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) \/ x1.
Definition term80 (x0 : real) (x1 : real) (x2 : real) := and ((fun y0 : real => ((real_add x0 y0) = (real_add x1 y0)) \/ (~ (x0 = x1))) x2).
Definition term188 (x0 : real) := (fun y0 : real => (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term240 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term233 (x0 : real) (x1 : real) := ~ ((real_mul x1 (real_add (real_neg x0) x0)) = (real_mul x1 (real_of_num (NUMERAL 0)))).
Definition term271 (x0 : real) (x1 : real) := ~ ((real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1))).
Definition term263 (x0 : real) (x1 : real) := ~ ((real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1))).
Definition term239 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term84 (x0 : real) (x1 : real) (x2 : real) := ((fun y0 : real => ((real_add x0 y0) = (real_add x1 y0)) \/ (~ (x0 = x1))) x2) /\ ((fun y0 : real => (~ ((real_add x0 y0) = (real_add x1 y0))) \/ (x0 = x1)) x2).
Definition term27 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_add x1 x2).
Definition term136 (x0 : real) (x1 : real) := ((forall y0 : real, (real_add x0 y0) = (real_add x1 y0)) \/ (~ (x0 = x1))) /\ ((forall y0 : real, ~ ((real_add x0 y0) = (real_add x1 y0))) \/ (x0 = x1)).
Definition term146 (x0 : real) (x1 : real) := ((fun y0 : real => (forall y1 : real, (real_add x0 y1) = (real_add y0 y1)) \/ (~ (x0 = y0))) x1) /\ ((fun y0 : real => (forall y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) \/ (x0 = y0)) x1).
Definition term265 (x0 : real) (x1 : real) := (((real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)) = (real_of_num (NUMERAL 0))) /\ ((real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)))) -> (real_of_num (NUMERAL 0)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)).
Definition term193 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (~ ((real_add x0 y1) = (real_add y0 y1))) \/ (x0 = y0)) x1.
Definition term190 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul x0 (real_add y0 y1)) = (real_add (real_mul x0 y0) (real_mul x0 y1))) x1.
Definition term182 (x0 : real) (x1 : real) := @eq Prop ((forall y0 : real, ~ ((real_add x0 y0) = (real_add x1 y0))) \/ (x0 = x1)).
Definition term181 (x0 : real) (x1 : real) := @eq Prop ((forall y0 : real, (fun y1 : real => ~ ((real_add x0 y1) = (real_add x1 y1))) y0) \/ (x0 = x1)).
Definition term223 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term121 (x0 : real) (x1 : real) := fun y0 : real => ~ ((real_add x0 y0) = (real_add x1 y0)).
Definition term61 := fun y0 : real => exists y1 : real, ~ ((real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))).
Definition term278 (x0 : real) (x1 : real) (x2 : real) := imp ((real_add x0 x2) = (real_add x1 x2)).
Definition term143 (x0 : real) (x1 : real) := (fun y0 : real => (forall y1 : real, (real_add x0 y1) = (real_add y0 y1)) \/ (~ (x0 = y0))) x1.
Definition term105 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_add x0 y0) = (real_add x1 y0)) x2.
Definition term16 := (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> ~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)).
Definition term63 (x0 : real) (x1 : real) (x2 : real) := (((real_add x1 x0) = (real_add x2 x0)) \/ (~ (x1 = x2))) /\ ((~ ((real_add x1 x0) = (real_add x2 x0))) \/ (x1 = x2)).
Definition term112 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => (real_add x0 y1) = (real_add x1 y1)) y0.
Definition term209 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 = x1)) \/ (((real_mul x0 x2) = (real_mul x1 x3)) \/ (~ (x2 = x3))).
Definition term273 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ ((real_add x1 x0) = (real_add x2 x0))) \/ (x1 = x2)).
Definition term185 := fun y0 : real => forall y1 : real, forall y2 : real, (~ ((real_add y0 y2) = (real_add y1 y2))) \/ (y0 = y1).
Definition term68 := fun y0 : real => forall y1 : real, forall y2 : real, (((real_add y0 y2) = (real_add y1 y2)) \/ (~ (y0 = y1))) /\ ((~ ((real_add y0 y2) = (real_add y1 y2))) \/ (y0 = y1)).
Definition term33 := fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2)).
Definition term26 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1).
Definition term76 (x0 : real) (x1 : real) := fun y0 : real => ((real_add x0 y0) = (real_add x1 y0)) \/ (~ (x0 = x1)).
Definition term40 := fun y0 : real => (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)).
Definition term207 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_mul x0 x2) = (real_mul x1 x3)) \/ (~ (x2 = x3)).
Definition term160 := forall y0 : real, (forall y1 : real, (forall y2 : real, (real_add y0 y2) = (real_add y1 y2)) \/ (~ (y0 = y1))) /\ (forall y1 : real, (forall y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) \/ (y0 = y1)).
Definition term282 (x0 : real) (x1 : real) := ((real_mul x0 (real_neg x1)) = (real_neg (real_mul x0 x1))) -> False.
Definition term109 (x0 : real) (x1 : real) := fun y0 : real => ((fun y1 : real => (real_add x0 y1) = (real_add x1 y1)) y0) \/ (~ (x0 = x1)).
Definition term225 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x0 = x1) /\ (x2 = x3).
Definition term250 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term245 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term219 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term206 (x0 : real) := ~ ((real_add (real_neg x0) x0) = (real_of_num (NUMERAL 0))).
Definition term243 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term275 (x0 : real) (x1 : real) (x2 : real) := (~ (~ ((real_add x1 x0) = (real_add x2 x0)))) -> x1 = x2.
Definition term107 (x0 : real) (x1 : real) (x2 : real) := or ((real_add x0 x2) = (real_add x1 x2)).
Definition term178 := forall y0 : real, (fun y1 : real => forall y2 : real, (forall y3 : real, ~ ((real_add y1 y3) = (real_add y2 y3))) \/ (y1 = y2)) y0.
Definition term173 := forall y0 : real, (fun y1 : real => forall y2 : real, (forall y3 : real, (real_add y1 y3) = (real_add y2 y3)) \/ (~ (y1 = y2))) y0.
Definition term224 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term168 (x0 : real) := ((fun y0 : real => forall y1 : real, (forall y2 : real, (real_add y0 y2) = (real_add y1 y2)) \/ (~ (y0 = y1))) x0) /\ ((fun y0 : real => forall y1 : real, (forall y2 : real, ~ ((real_add y0 y2) = (real_add y1 y2))) \/ (y0 = y1)) x0).
Definition term13 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> ~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)).
Definition term254 (x0 : real) (x1 : real) := ~ ((real_mul x0 (real_of_num (NUMERAL 0))) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1))).
Definition term123 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_add x0 x2) = (real_add x1 x2)).
Definition term195 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term204 (x0 : real) := ~ (x0 = x0).
Definition term147 (x0 : real) := fun y0 : real => ((fun y1 : real => (forall y2 : real, (real_add x0 y2) = (real_add y1 y2)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => (forall y2 : real, ~ ((real_add x0 y2) = (real_add y1 y2))) \/ (x0 = y1)) y0).
Definition term85 (x0 : real) (x1 : real) := fun y0 : real => ((fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) \/ (~ (x0 = x1))) y0) /\ ((fun y1 : real => (~ ((real_add x0 y1) = (real_add x1 y1))) \/ (x0 = x1)) y0).
Definition term155 (x0 : real) := fun y0 : real => (fun y1 : real => (forall y2 : real, ~ ((real_add x0 y2) = (real_add y1 y2))) \/ (x0 = y1)) y0.
Definition term93 (x0 : real) (x1 : real) := fun y0 : real => (fun y1 : real => (~ ((real_add x0 y1) = (real_add x1 y1))) \/ (x0 = x1)) y0.
Definition term132 (x0 : real) (x1 : real) := forall y0 : real, ~ ((real_add x0 y0) = (real_add x1 y0)).
Definition term17 := imp (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
Definition term14 := imp (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))).
Definition term216 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 = x1)) \/ (~ (x2 = x3)).
Definition term39 (x0 : real) := real_mul x0 (real_of_num (NUMERAL 0)).
Definition term41 := forall y0 : real, (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0)).
Definition term54 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_mul x0 (real_neg y1)) = (real_neg (real_mul x0 y1))) y0).
Definition term191 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul x1 (real_add x0 y0)) = (real_add (real_mul x1 x0) (real_mul x1 y0))) x2.
Definition term73 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term252 (x0 : real) (x1 : real) := (((real_mul x0 (real_add (real_neg x1) x1)) = (real_mul x0 (real_of_num (NUMERAL 0)))) /\ ((real_mul x0 (real_add (real_neg x1) x1)) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1)))) -> (real_mul x0 (real_of_num (NUMERAL 0))) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1)).
Definition term198 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((real_mul x0 x1) = (real_mul x2 x3))).
Definition term77 (x0 : real) (x1 : real) := fun y0 : real => (~ ((real_add x0 y0) = (real_add x1 y0))) \/ (x0 = x1).
Definition term249 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term264 (x0 : real) (x1 : real) := ((real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)) = (real_of_num (NUMERAL 0))) /\ ((real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1))).
Definition term141 (x0 : real) := fun y0 : real => (forall y1 : real, (real_add x0 y1) = (real_add y0 y1)) \/ (~ (x0 = y0)).
Definition term55 (x0 : real) := fun y0 : real => ~ ((real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0))).
Definition term270 (x0 : real) (x1 : real) := (~ ((real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)))) -> (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)).
Definition term262 (x0 : real) (x1 : real) := (~ ((real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)))) -> (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)).
Definition term137 (x0 : real) := fun y0 : real => ((forall y1 : real, (real_add x0 y1) = (real_add y0 y1)) \/ (~ (x0 = y0))) /\ ((forall y1 : real, ~ ((real_add x0 y1) = (real_add y0 y1))) \/ (x0 = y0)).
Definition term124 (x0 : real) (x1 : real) (x2 : real) := or ((fun y0 : real => ~ ((real_add x0 y0) = (real_add x1 y0))) x2).
Definition term21 := (~ (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)))) -> (forall y0 : real, (real_mul y0 (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> ~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)).
Definition term237 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term222 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term144 (x0 : real) (x1 : real) := and ((fun y0 : real => (forall y1 : real, (real_add x0 y1) = (real_add y0 y1)) \/ (~ (x0 = y0))) x1).
Definition term208 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term102 (x0 : real) (x1 : real) := (forall y0 : real, (fun y1 : real => (real_add x0 y1) = (real_add x1 y1)) y0) \/ (~ (x0 = x1)).
Definition term29 (x0 : real) (x1 : real) := fun y0 : real => (real_mul x1 (real_add x0 y0)) = (real_add (real_mul x1 x0) (real_mul x1 y0)).
Definition term268 (x0 : real) (x1 : real) := ((real_of_num (NUMERAL 0)) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1))) /\ ((real_of_num (NUMERAL 0)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1))).
Definition term64 (x0 : real) (x1 : real) := fun y0 : real => (((real_add x0 y0) = (real_add x1 y0)) \/ (~ (x0 = x1))) /\ ((~ ((real_add x0 y0) = (real_add x1 y0))) \/ (x0 = x1)).
Definition term192 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (~ ((real_add y0 y2) = (real_add y1 y2))) \/ (y0 = y1)) x0.
Definition term189 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) x0.
Definition term15 := (forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_add y0 y2) = (real_add y1 y2)) = (y0 = y1)) -> False.
Definition term90 (x0 : real) (x1 : real) := forall y0 : real, ((real_add x0 y0) = (real_add x1 y0)) \/ (~ (x0 = x1)).
Definition term161 := forall y0 : real, ((fun y1 : real => forall y2 : real, (forall y3 : real, (real_add y1 y3) = (real_add y2 y3)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : real => forall y2 : real, (forall y3 : real, ~ ((real_add y1 y3) = (real_add y2 y3))) \/ (y1 = y2)) y0).
Definition term139 (x0 : real) := forall y0 : real, ((fun y1 : real => (forall y2 : real, (real_add x0 y2) = (real_add y1 y2)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : real => (forall y2 : real, ~ ((real_add x0 y2) = (real_add y1 y2))) \/ (x0 = y1)) y0).
Definition term74 (x0 : real) (x1 : real) := forall y0 : real, ((fun y1 : real => ((real_add x0 y1) = (real_add x1 y1)) \/ (~ (x0 = x1))) y0) /\ ((fun y1 : real => (~ ((real_add x0 y1) = (real_add x1 y1))) \/ (x0 = x1)) y0).
Definition term20 := imp (~ (forall y0 : real, forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)))).
Definition term163 := fun y0 : real => forall y1 : real, (forall y2 : real, (real_add y0 y2) = (real_add y1 y2)) \/ (~ (y0 = y1)).
Definition term46 := fun y0 : real => forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1)).
Definition term276 (x0 : real) (x1 : real) (x2 : real) := ~ (~ ((real_add x0 x2) = (real_add x1 x2))).
Definition term269 (x0 : real) (x1 : real) := (((real_of_num (NUMERAL 0)) = (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1))) /\ ((real_of_num (NUMERAL 0)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)))) -> (real_add (real_mul x0 (real_neg x1)) (real_mul x0 x1)) = (real_add (real_neg (real_mul x0 x1)) (real_mul x0 x1)).
