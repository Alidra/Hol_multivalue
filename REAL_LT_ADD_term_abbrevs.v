Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term36 (x0 : real) (x1 : real) := ~ (((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1)).
Definition term68 (x0 : real) (x1 : real) := (~ (real_lt x0 x1)) \/ (real_le x0 x1).
Definition term40 (x0 : real -> Prop) := ~ (all x0).
Definition term120 := (~ False) -> False.
Definition term98 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_add x1 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term18 := imp (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)).
Definition term76 (x0 : real) (x1 : real) := (fun y0 : real => (~ (real_lt x0 y0)) \/ (real_le x0 y0)) x1.
Definition term77 (x0 : real) (x1 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1))).
Definition term89 (x0 : Prop) := ~ (~ x0).
Definition term94 := real_of_num (NUMERAL 0).
Definition term81 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) -> real_lt (real_of_num (NUMERAL 0)) x0.
Definition term100 (x0 : real) (x1 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ ((real_lt (real_of_num (NUMERAL 0)) (real_add x1 x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x1))).
Definition term103 (x0 : real) (x1 : real) := @eq Prop ((real_lt (real_of_num (NUMERAL 0)) (real_add x1 x0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x1)))).
Definition term44 (x0 : real) (x1 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_add x0 y0)) x1.
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term105 (x0 : real) (x1 : real) := or (real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1)).
Definition term116 (x0 : real) (x1 : real) := imp (~ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1)))).
Definition term42 (x0 : real) := ~ (forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_add x0 y0)).
Definition term61 (x0 : real) (x1 : real) := (~ ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1))) \/ (real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1)).
Definition term24 (x0 : real) := fun y0 : real => (real_lt x0 y0) -> real_le x0 y0.
Definition term45 (x0 : real) (x1 : real) := ~ ((fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_add x0 y0)) x1).
Definition term87 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term82 (x0 : Prop) := (~ x0) -> x0.
Definition term86 (x0 : real) (x1 : real) := @eq Prop ((real_le x0 x1) \/ (~ (real_lt x0 x1))).
Definition term12 := ((~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> False) -> (~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> False.
Definition term59 (x0 : real) (x1 : real) := or (~ ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1))).
Definition term74 (x0 : real) (x1 : real) := (fun y0 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) y0))) \/ (real_lt (real_of_num (NUMERAL 0)) (real_add x0 y0))) x1.
Definition term109 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term79 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term88 (x0 : real) (x1 : real) := (~ (~ (real_lt x0 x1))) -> real_le x0 x1.
Definition term72 := forall y0 : real, forall y1 : real, (~ (real_lt y0 y1)) \/ (real_le y0 y1).
Definition term67 := forall y0 : real, forall y1 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) y1))) \/ (real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)).
Definition term31 := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1).
Definition term17 := forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1.
Definition term8 := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1).
Definition term85 (x0 : real) (x1 : real) := @eq Prop ((~ (real_lt x0 x1)) \/ (real_le x0 x1)).
Definition term54 := exists y0 : real, exists y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ (real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))).
Definition term23 (x0 : real) (x1 : real) := (real_lt x0 x1) -> real_le x0 x1.
Definition term56 (x0 : real) (x1 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1)).
Definition term19 := (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> False.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term22 := (~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)) -> ~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1).
Definition term114 (x0 : real) := and (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term78 (x0 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term95 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term106 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1)) \/ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1))).
Definition term34 (x0 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_add x0 y0).
Definition term29 (x0 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_add x0 y0).
Definition term37 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) /\ (~ (real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1))).
Definition term69 (x0 : real) := fun y0 : real => (~ (real_lt x0 y0)) \/ (real_le x0 y0).
Definition term49 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_of_num (NUMERAL 0)) y2)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y1 y2)) y0).
Definition term43 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add x0 y1)) y0).
Definition term52 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_of_num (NUMERAL 0)) y2)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y1 y2)) y0).
Definition term33 (x0 : real) := fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_add x0 y0).
Definition term28 (x0 : real) := fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_add x0 y0).
Definition term99 (x0 : real) := or (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term53 := fun y0 : real => exists y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) /\ (~ (real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))).
Definition term39 (x0 : real) (x1 : real) := real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term66 := fun y0 : real => forall y1 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) y1))) \/ (real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)).
Definition term35 := fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1).
Definition term30 := fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1).
Definition term118 (x0 : real) (x1 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1))) -> real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term15 := (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> False.
Definition term112 (x0 : real) := ~ (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term16 := ~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1).
Definition term10 := ~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)).
Definition term32 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term27 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term84 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term62 (x0 : real) (x1 : real) := ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1))) \/ (real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1)).
Definition term108 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term97 (x0 : real) (x1 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1)).
Definition term51 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)) x0).
Definition term102 (x0 : real) (x1 : real) := @eq Prop ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ (real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1)))).
Definition term13 := (((~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> False) -> (~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> False) -> (~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> False.
Definition term71 := fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (real_le y0 y1).
Definition term26 := fun y0 : real => forall y1 : real, (real_lt y0 y1) -> real_le y0 y1.
Definition term41 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term104 (x0 : real) (x1 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term92 (x0 : real) (x1 : real) := imp (real_lt x0 x1).
Definition term75 (x0 : real) := (fun y0 : real => forall y1 : real, (~ (real_lt y0 y1)) \/ (real_le y0 y1)) x0.
Definition term73 (x0 : real) := (fun y0 : real => forall y1 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) y0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) y1))) \/ (real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))) x0.
Definition term50 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)) x0.
Definition term63 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1).
Definition term48 (x0 : real) := exists y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ (real_lt (real_of_num (NUMERAL 0)) (real_add x0 y0))).
Definition term25 (x0 : real) := forall y0 : real, (real_lt x0 y0) -> real_le x0 y0.
Definition term60 (x0 : real) (x1 : real) := or ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1))).
Definition term58 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term9 := (~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> False.
Definition term38 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1).
Definition term55 (x0 : real) (x1 : real) := ~ ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)).
Definition term14 := (((~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> False) -> (~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> False) -> ((~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> False) -> (~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> False.
Definition term113 (x0 : real) := and (~ (~ (real_lt (real_of_num (NUMERAL 0)) x0))).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term57 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term64 (x0 : real) := fun y0 : real => ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) y0))) \/ (real_lt (real_of_num (NUMERAL 0)) (real_add x0 y0)).
Definition term90 (x0 : real) (x1 : real) := ~ (~ (real_lt x0 x1)).
Definition term119 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1)) -> False.
Definition term80 (x0 : real) (x1 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1)).
Definition term96 (x0 : real) (x1 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x1)) \/ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1))).
Definition term83 (x0 : real) (x1 : real) := (real_le x0 x1) \/ (~ (real_lt x0 x1)).
Definition term117 (x0 : real) (x1 : real) := imp ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)).
Definition term70 (x0 : real) := forall y0 : real, (~ (real_lt x0 y0)) \/ (real_le x0 y0).
Definition term110 (x0 : real) (x1 : real) := ~ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1))).
Definition term20 := (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)) -> ~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term46 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add x0 y1)) y0).
Definition term111 (x0 : real) (x1 : real) := (~ (~ (real_lt (real_of_num (NUMERAL 0)) x0))) /\ (~ (~ (real_le (real_of_num (NUMERAL 0)) x1))).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term65 (x0 : real) := forall y0 : real, ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) y0))) \/ (real_lt (real_of_num (NUMERAL 0)) (real_add x0 y0)).
Definition term93 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term47 (x0 : real) := fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) /\ (~ (real_lt (real_of_num (NUMERAL 0)) (real_add x0 y0))).
Definition term107 (x0 : real) (x1 : real) := (~ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_le (real_of_num (NUMERAL 0)) x1)))) -> real_lt (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term115 (x0 : real) := ~ (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term11 := (~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1)) -> (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_le y0 y1) -> False.
Definition term21 := imp (~ (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_add y0 y1))).
Definition term91 (x0 : real) (x1 : real) := imp (~ (~ (real_lt x0 x1))).
Definition term101 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_add x1 x0)) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x1))).