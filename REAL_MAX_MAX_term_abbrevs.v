Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term178 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term139 (x0 : real) (x1 : real) := (fun y0 : real => real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0))) x1.
Definition term135 (x0 : real) (x1 : real) := (fun y0 : real => real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0))) x1.
Definition term163 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term56 (x0 : real -> Prop) := ~ (all x0).
Definition term110 := (exists y0 : real, exists y1 : real, real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, exists y1 : real, real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))).
Definition term87 := (exists y0 : real, exists y1 : real, ~ (real_le y0 (real_max y0 y1))) \/ (exists y0 : real, exists y1 : real, ~ (real_le y1 (real_max y0 y1))).
Definition term93 := real_of_num (NUMERAL 0).
Definition term49 := and (forall y0 : real, forall y1 : real, real_le y0 (real_max y0 y1)).
Definition term25 (x0 : real) := and (forall y0 : real, real_le x0 (real_max x0 y0)).
Definition term39 (x0 : real) := and ((fun y0 : real => forall y1 : real, real_le y0 (real_max y0 y1)) x0).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term153 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x1 x2))) x3.
Definition term48 := and (forall y0 : real, (fun y1 : real => forall y2 : real, real_le y1 (real_max y1 y2)) y0).
Definition term24 (x0 : real) := and (forall y0 : real, (fun y1 : real => real_le x0 (real_max x0 y1)) y0).
Definition term101 (x0 : real) (x1 : real) := real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1)).
Definition term181 (x0 : real) (x1 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term71 (x0 : real) := ~ (forall y0 : real, real_le y0 (real_max x0 y0)).
Definition term58 (x0 : real) := ~ (forall y0 : real, real_le x0 (real_max x0 y0)).
Definition term12 (x0 : real) (x1 : real) := (fun y0 : real => real_le y0 (real_max x0 y0)) x1.
Definition term31 := fun y0 : real => (forall y1 : real, real_le y0 (real_max y0 y1)) /\ (forall y1 : real, real_le y1 (real_max y0 y1)).
Definition term126 (x0 : real) := or ((fun y0 : real => exists y1 : real, real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))) x0).
Definition term156 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term53 := (forall y0 : real, forall y1 : real, real_le y0 (real_max y0 y1)) /\ (forall y0 : real, forall y1 : real, real_le y1 (real_max y0 y1)).
Definition term73 (x0 : real) (x1 : real) := ~ ((fun y0 : real => real_le y0 (real_max x0 y0)) x1).
Definition term60 (x0 : real) (x1 : real) := ~ ((fun y0 : real => real_le x0 (real_max x0 y0)) x1).
Definition term61 (x0 : real) (x1 : real) := ~ (real_le x0 (real_max x0 x1)).
Definition term35 := (forall y0 : real, (fun y1 : real => forall y2 : real, real_le y1 (real_max y1 y2)) y0) /\ (forall y0 : real, (fun y1 : real => forall y2 : real, real_le y2 (real_max y1 y2)) y0).
Definition term5 (x0 : real) := (forall y0 : real, (fun y1 : real => real_le x0 (real_max x0 y1)) y0) /\ (forall y0 : real, (fun y1 : real => real_le y1 (real_max x0 y1)) y0).
Definition term23 (x0 : real) := forall y0 : real, real_le x0 (real_max x0 y0).
Definition term147 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1))) (real_of_num (NUMERAL 0))).
Definition term100 (x0 : real) (x1 : real) := real_sub x1 (real_max x0 x1).
Definition term175 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term50 := fun y0 : real => (fun y1 : real => forall y2 : real, real_le y2 (real_max y1 y2)) y0.
Definition term45 := fun y0 : real => (fun y1 : real => forall y2 : real, real_le y1 (real_max y1 y2)) y0.
Definition term6 (x0 : real) := fun y0 : real => real_le x0 (real_max x0 y0).
Definition term173 (x0 : real) (x1 : real) := (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term155 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term141 (x0 : real) := exists y0 : real, (fun y1 : real => real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1))) (real_of_num (NUMERAL 0))) y0.
Definition term137 (x0 : real) := exists y0 : real, (fun y1 : real => real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1))) (real_of_num (NUMERAL 0))) y0.
Definition term52 := forall y0 : real, forall y1 : real, real_le y1 (real_max y0 y1).
Definition term47 := forall y0 : real, forall y1 : real, real_le y0 (real_max y0 y1).
Definition term32 := forall y0 : real, forall y1 : real, (real_le y0 (real_max y0 y1)) /\ (real_le y1 (real_max y0 y1)).
Definition term84 := or (~ (forall y0 : real, forall y1 : real, real_le y0 (real_max y0 y1))).
Definition term152 := exists y0 : real, exists y1 : real, (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))).
Definition term108 := exists y0 : real, exists y1 : real, real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0)).
Definition term98 := exists y0 : real, exists y1 : real, real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0)).
Definition term83 := exists y0 : real, exists y1 : real, ~ (real_le y1 (real_max y0 y1)).
Definition term70 := exists y0 : real, exists y1 : real, ~ (real_le y0 (real_max y0 y1)).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term138 (x0 : real) := or (exists y0 : real, (fun y1 : real => real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1))) (real_of_num (NUMERAL 0))) y0).
Definition term120 := or (exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2))) (real_of_num (NUMERAL 0))) y0).
Definition term79 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, real_le y2 (real_max y1 y2)) y0).
Definition term72 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => real_le y1 (real_max x0 y1)) y0).
Definition term66 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, real_le y1 (real_max y1 y2)) y0).
Definition term59 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => real_le x0 (real_max x0 y1)) y0).
Definition term121 (x0 : real) := (fun y0 : real => exists y1 : real, real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))) x0.
Definition term117 (x0 : real) := (fun y0 : real => exists y1 : real, real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))) x0.
Definition term154 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) x3) /\ (real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)) x3).
Definition term177 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term74 (x0 : real) (x1 : real) := ~ (real_le x1 (real_max x0 x1)).
Definition term81 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, real_le y2 (real_max y1 y2)) y0).
Definition term68 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, real_le y1 (real_max y1 y2)) y0).
Definition term44 := @eq Prop (forall y0 : real, (forall y1 : real, real_le y0 (real_max y0 y1)) /\ (forall y1 : real, real_le y1 (real_max y0 y1))).
Definition term43 := @eq Prop (forall y0 : real, ((fun y1 : real => forall y2 : real, real_le y1 (real_max y1 y2)) y0) /\ ((fun y1 : real => forall y2 : real, real_le y2 (real_max y1 y2)) y0)).
Definition term20 (x0 : real) := @eq Prop (forall y0 : real, (real_le x0 (real_max x0 y0)) /\ (real_le y0 (real_max x0 y0))).
Definition term19 (x0 : real) := @eq Prop (forall y0 : real, ((fun y1 : real => real_le x0 (real_max x0 y1)) y0) /\ ((fun y1 : real => real_le y1 (real_max x0 y1)) y0)).
Definition term107 := fun y0 : real => exists y1 : real, real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0)).
Definition term97 := fun y0 : real => exists y1 : real, real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0)).
Definition term171 := and (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term30 := fun y0 : real => forall y1 : real, (real_le y0 (real_max y0 y1)) /\ (real_le y1 (real_max y0 y1)).
Definition term15 (x0 : real) (x1 : real) := (real_le x0 (real_max x0 x1)) /\ (real_le x1 (real_max x0 x1)).
Definition term128 (x0 : real) := ((fun y0 : real => exists y1 : real, real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => exists y1 : real, real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))) x0).
Definition term160 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term114 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term129 (x0 : real) := (exists y0 : real, real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0))).
Definition term78 := ~ (forall y0 : real, forall y1 : real, real_le y1 (real_max y0 y1)).
Definition term65 := ~ (forall y0 : real, forall y1 : real, real_le y0 (real_max y0 y1)).
Definition term54 := ~ (forall y0 : real, forall y1 : real, (real_le y0 (real_max y0 y1)) /\ (real_le y1 (real_max y0 y1))).
Definition term186 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term106 (x0 : real) := exists y0 : real, real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0)).
Definition term96 (x0 : real) := exists y0 : real, real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0)).
Definition term122 := fun y0 : real => (fun y1 : real => exists y2 : real, real_gt (real_add y2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2))) (real_of_num (NUMERAL 0))) y0.
Definition term118 := fun y0 : real => (fun y1 : real => exists y2 : real, real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2))) (real_of_num (NUMERAL 0))) y0.
Definition term77 (x0 : real) := exists y0 : real, ~ (real_le y0 (real_max x0 y0)).
Definition term64 (x0 : real) := exists y0 : real, ~ (real_le x0 (real_max x0 y0)).
Definition term113 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term169 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term29 (x0 : real) := (forall y0 : real, real_le x0 (real_max x0 y0)) /\ (forall y0 : real, real_le y0 (real_max x0 y0)).
Definition term11 (x0 : real) (x1 : real) := and (real_le x0 (real_max x0 x1)).
Definition term99 (x0 : real) (x1 : real) := real_gt (real_sub x1 (real_max x0 x1)) (real_of_num (NUMERAL 0)).
Definition term80 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, real_le y1 (real_max y0 y1)) x0).
Definition term67 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, real_le y0 (real_max y0 y1)) x0).
Definition term151 := fun y0 : real => exists y1 : real, (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))).
Definition term180 (x0 : real) (x1 : real) := and (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term170 (x0 : real) := and (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))).
Definition term172 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term57 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term2 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term149 (x0 : real) := fun y0 : real => (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0))).
Definition term105 (x0 : real) := fun y0 : real => real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0)).
Definition term95 (x0 : real) := fun y0 : real => real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0)).
Definition term40 (x0 : real) := (fun y0 : real => forall y1 : real, real_le y1 (real_max y0 y1)) x0.
Definition term38 (x0 : real) := (fun y0 : real => forall y1 : real, real_le y0 (real_max y0 y1)) x0.
Definition term184 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term185 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term145 (x0 : real) (x1 : real) := or (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1))) (real_of_num (NUMERAL 0))).
Definition term158 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term159 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term182 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term187 := (~ (forall y0 : real, forall y1 : real, (real_le y0 (real_max y0 y1)) /\ (real_le y1 (real_max y0 y1)))) -> False.
Definition term27 (x0 : real) := forall y0 : real, (fun y1 : real => real_le y1 (real_max x0 y1)) y0.
Definition term22 (x0 : real) := forall y0 : real, (fun y1 : real => real_le x0 (real_max x0 y1)) y0.
Definition term104 (x0 : real) (x1 : real) := real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1))) (real_of_num (NUMERAL 0)).
Definition term76 (x0 : real) := fun y0 : real => ~ (real_le y0 (real_max x0 y0)).
Definition term28 (x0 : real) := forall y0 : real, real_le y0 (real_max x0 y0).
Definition term9 (x0 : real) (x1 : real) := real_le x0 (real_max x0 x1).
Definition term42 := fun y0 : real => ((fun y1 : real => forall y2 : real, real_le y1 (real_max y1 y2)) y0) /\ ((fun y1 : real => forall y2 : real, real_le y2 (real_max y1 y2)) y0).
Definition term18 (x0 : real) := forall y0 : real, (real_le x0 (real_max x0 y0)) /\ (real_le y0 (real_max x0 y0)).
Definition term102 (x0 : real) (x1 : real) := real_gt (real_sub x1 (real_max x0 x1)).
Definition term164 := real_mul (real_of_num (NUMERAL 0)).
Definition term14 (x0 : real) (x1 : real) := ((fun y0 : real => real_le x0 (real_max x0 y0)) x1) /\ ((fun y0 : real => real_le y0 (real_max x0 y0)) x1).
Definition term55 := ~ ((forall y0 : real, forall y1 : real, real_le y0 (real_max y0 y1)) /\ (forall y0 : real, forall y1 : real, real_le y1 (real_max y0 y1))).
Definition term176 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term103 (x0 : real) (x1 : real) := real_gt (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1))).
Definition term82 := fun y0 : real => exists y1 : real, ~ (real_le y1 (real_max y0 y1)).
Definition term69 := fun y0 : real => exists y1 : real, ~ (real_le y0 (real_max y0 y1)).
Definition term148 (x0 : real) := fun y0 : real => ((fun y1 : real => real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1))) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1))) (real_of_num (NUMERAL 0))) y0).
Definition term90 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1)).
Definition term89 (x0 : real) (x1 : real) := real_sub x0 (real_max x0 x1).
Definition term134 (x0 : real) := exists y0 : real, ((fun y1 : real => real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1))) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1))) (real_of_num (NUMERAL 0))) y0).
Definition term116 := exists y0 : real, ((fun y1 : real => exists y2 : real, real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2))) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => exists y2 : real, real_gt (real_add y2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2))) (real_of_num (NUMERAL 0))) y0).
Definition term188 := ((~ (forall y0 : real, forall y1 : real, (real_le y0 (real_max y0 y1)) /\ (real_le y1 (real_max y0 y1)))) -> False) -> forall y0 : real, forall y1 : real, (real_le y0 (real_max y0 y1)) /\ (real_le y1 (real_max y0 y1)).
Definition term37 := fun y0 : real => forall y1 : real, real_le y1 (real_max y0 y1).
Definition term36 := fun y0 : real => forall y1 : real, real_le y0 (real_max y0 y1).
Definition term166 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term144 (x0 : real) (x1 : real) := or ((fun y0 : real => real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0))) x1).
Definition term33 := forall y0 : real, (forall y1 : real, real_le y0 (real_max y0 y1)) /\ (forall y1 : real, real_le y1 (real_max y0 y1)).
Definition term92 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1))).
Definition term26 (x0 : real) := fun y0 : real => (fun y1 : real => real_le y1 (real_max x0 y1)) y0.
Definition term21 (x0 : real) := fun y0 : real => (fun y1 : real => real_le x0 (real_max x0 y1)) y0.
Definition term168 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term88 (x0 : real) (x1 : real) := real_gt (real_sub x0 (real_max x0 x1)) (real_of_num (NUMERAL 0)).
Definition term51 := forall y0 : real, (fun y1 : real => forall y2 : real, real_le y2 (real_max y1 y2)) y0.
Definition term46 := forall y0 : real, (fun y1 : real => forall y2 : real, real_le y1 (real_max y1 y2)) y0.
Definition term140 (x0 : real) := fun y0 : real => (fun y1 : real => real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1))) (real_of_num (NUMERAL 0))) y0.
Definition term136 (x0 : real) := fun y0 : real => (fun y1 : real => real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1))) (real_of_num (NUMERAL 0))) y0.
Definition term146 (x0 : real) (x1 : real) := ((fun y0 : real => real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0))) x1) \/ ((fun y0 : real => real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0))) x1).
Definition term165 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term41 (x0 : real) := ((fun y0 : real => forall y1 : real, real_le y0 (real_max y0 y1)) x0) /\ ((fun y0 : real => forall y1 : real, real_le y1 (real_max y0 y1)) x0).
Definition term183 (x0 : real) (x1 : real) := or ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))).
Definition term16 (x0 : real) := fun y0 : real => ((fun y1 : real => real_le x0 (real_max x0 y1)) y0) /\ ((fun y1 : real => real_le y1 (real_max x0 y1)) y0).
Definition term86 := (~ (forall y0 : real, forall y1 : real, real_le y0 (real_max y0 y1))) \/ (~ (forall y0 : real, forall y1 : real, real_le y1 (real_max y0 y1))).
Definition term75 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => real_le y1 (real_max x0 y1)) y0).
Definition term62 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => real_le x0 (real_max x0 y1)) y0).
Definition term3 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term17 (x0 : real) := fun y0 : real => (real_le x0 (real_max x0 y0)) /\ (real_le y0 (real_max x0 y0)).
Definition term63 (x0 : real) := fun y0 : real => ~ (real_le x0 (real_max x0 y0)).
Definition term174 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term161 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term10 (x0 : real) (x1 : real) := and ((fun y0 : real => real_le x0 (real_max x0 y0)) x1).
Definition term132 := exists y0 : real, (exists y1 : real, real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))) \/ (exists y1 : real, real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))).
Definition term130 := fun y0 : real => ((fun y1 : real => exists y2 : real, real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2))) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => exists y2 : real, real_gt (real_add y2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2))) (real_of_num (NUMERAL 0))) y0).
Definition term13 (x0 : real) (x1 : real) := real_le x1 (real_max x0 x1).
Definition term127 (x0 : real) := or (exists y0 : real, real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0))).
Definition term109 := or (exists y0 : real, exists y1 : real, real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))).
Definition term85 := or (exists y0 : real, exists y1 : real, ~ (real_le y0 (real_max y0 y1))).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term179 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term131 := fun y0 : real => (exists y1 : real, real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))) \/ (exists y1 : real, real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))).
Definition term34 := forall y0 : real, ((fun y1 : real => forall y2 : real, real_le y1 (real_max y1 y2)) y0) /\ ((fun y1 : real => forall y2 : real, real_le y2 (real_max y1 y2)) y0).
Definition term4 (x0 : real) := forall y0 : real, ((fun y1 : real => real_le x0 (real_max x0 y1)) y0) /\ ((fun y1 : real => real_le y1 (real_max x0 y1)) y0).
Definition term162 := NUMERAL (BIT1 0).
Definition term133 (x0 : real) := (exists y0 : real, (fun y1 : real => real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1))) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1))) (real_of_num (NUMERAL 0))) y0).
Definition term115 := (exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2))) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add y2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2))) (real_of_num (NUMERAL 0))) y0).
Definition term150 (x0 : real) := exists y0 : real, (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0))).
Definition term157 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term7 (x0 : real) := fun y0 : real => real_le y0 (real_max x0 y0).
Definition term94 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 x1))) (real_of_num (NUMERAL 0)).
Definition term8 (x0 : real) (x1 : real) := (fun y0 : real => real_le x0 (real_max x0 y0)) x1.
Definition term123 := exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add y2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2))) (real_of_num (NUMERAL 0))) y0.
Definition term119 := exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2))) (real_of_num (NUMERAL 0))) y0.
Definition term91 (x0 : real) (x1 : real) := real_gt (real_sub x0 (real_max x0 x1)).
Definition term167 := real_gt (real_of_num (NUMERAL 0)).
Definition term143 (x0 : real) := @eq Prop ((exists y0 : real, real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y0))) (real_of_num (NUMERAL 0)))).
Definition term142 (x0 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1))) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max x0 y1))) (real_of_num (NUMERAL 0))) y0)).
Definition term125 := @eq Prop ((exists y0 : real, exists y1 : real, real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, exists y1 : real, real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y0 y1))) (real_of_num (NUMERAL 0)))).
Definition term124 := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2))) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, real_gt (real_add y2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_max y1 y2))) (real_of_num (NUMERAL 0))) y0)).