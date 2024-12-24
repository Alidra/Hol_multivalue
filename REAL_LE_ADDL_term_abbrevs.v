Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term125 (x0 : real) (x1 : real) := (fun y0 : real => real_ge x0 (real_of_num (NUMERAL 0))) x1.
Definition term122 (x0 : real) := exists y0 : real, (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((fun y1 : real => real_ge x0 (real_of_num (NUMERAL 0))) y0).
Definition term108 (x0 : real) := exists y0 : real, (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y1 : real => real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) y0).
Definition term87 (x0 : real) := fun y0 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term35 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term23 (x0 : real) (x1 : real) := real_ge (real_sub (real_add x0 x1) x1) (real_of_num (NUMERAL 0)).
Definition term1 (x0 : real) (x1 : real) := ((real_le x0 (real_add x1 x0)) /\ (~ (real_le (real_of_num (NUMERAL 0)) x1))) \/ ((~ (real_le x0 (real_add x1 x0))) /\ (real_le (real_of_num (NUMERAL 0)) x1)).
Definition term4 (x0 : real -> Prop) := ~ (all x0).
Definition term176 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term172 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term162 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term12 (x0 : real) := fun y0 : real => ((real_le y0 (real_add x0 y0)) /\ (~ (real_le (real_of_num (NUMERAL 0)) x0))) \/ ((~ (real_le y0 (real_add x0 y0))) /\ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term133 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (exists y0 : real, real_ge x0 (real_of_num (NUMERAL 0))).
Definition term32 := real_of_num (NUMERAL 0).
Definition term56 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1).
Definition term107 (x0 : Prop) (x1 : real -> Prop) := x0 /\ (exists y0 : real, x1 y0).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term104 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term6 (x0 : real) := ~ (forall y0 : real, (real_le y0 (real_add x0 y0)) = (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term18 (x0 : real) := forall y0 : real, (real_le y0 (real_add x0 y0)) = (real_le (real_of_num (NUMERAL 0)) x0).
Definition term166 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term71 (x0 : real) (x1 : real) := (~ (real_le x0 (real_add x1 x0))) /\ (real_le (real_of_num (NUMERAL 0)) x1).
Definition term154 := exists y0 : real, (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))) /\ (real_ge y0 (real_of_num (NUMERAL 0))).
Definition term102 (x0 : real) := exists y0 : real, (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term42 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL 0)).
Definition term9 (x0 : real) (x1 : real) := (fun y0 : real => (real_le y0 (real_add x0 y0)) = (real_le (real_of_num (NUMERAL 0)) x0)) x1.
Definition term10 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_le y0 (real_add x0 y0)) = (real_le (real_of_num (NUMERAL 0)) x0)) x1).
Definition term124 (x0 : real) := fun y0 : real => real_ge x0 (real_of_num (NUMERAL 0)).
Definition term40 (x0 : real) := real_ge x0 (real_of_num (NUMERAL 0)).
Definition term54 (x0 : real) (x1 : real) := real_sub x1 (real_add x0 x1).
Definition term105 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term111 (x0 : real) (x1 : real) := (fun y0 : real => real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) x1.
Definition term61 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term49 (x0 : real) := and (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term38 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term41 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term160 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term123 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (exists y0 : real, (fun y1 : real => real_ge x0 (real_of_num (NUMERAL 0))) y0).
Definition term45 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) x0).
Definition term121 (x0 : Prop) := exists y0 : real, x0.
Definition term153 := exists y0 : real, (fun y1 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0))) /\ (real_ge y1 (real_of_num (NUMERAL 0)))) y0.
Definition term148 := exists y0 : real, (fun y1 : real => (real_ge y1 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0.
Definition term131 (x0 : real) := exists y0 : real, (fun y1 : real => real_ge x0 (real_of_num (NUMERAL 0))) y0.
Definition term117 (x0 : real) := exists y0 : real, (fun y1 : real => real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) y0.
Definition term101 (x0 : real) := exists y0 : real, (fun y1 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) y0.
Definition term96 (x0 : real) := exists y0 : real, (fun y1 : real => (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) y0.
Definition term118 (x0 : real) := exists y0 : real, real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term66 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term185 := forall y0 : real, forall y1 : real, (real_le y1 (real_add y0 y1)) = (real_le (real_of_num (NUMERAL 0)) y0).
Definition term79 := exists y0 : real, exists y1 : real, ((real_ge y0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))) /\ (real_ge y0 (real_of_num (NUMERAL 0)))).
Definition term22 := exists y0 : real, exists y1 : real, ((real_le y1 (real_add y0 y1)) /\ (~ (real_le (real_of_num (NUMERAL 0)) y0))) \/ ((~ (real_le y1 (real_add y0 y1))) /\ (real_le (real_of_num (NUMERAL 0)) y0)).
Definition term106 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 /\ (x1 y0).
Definition term150 := or (exists y0 : real, (fun y1 : real => (real_ge y1 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0).
Definition term98 (x0 : real) := or (exists y0 : real, (fun y1 : real => (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) y0).
Definition term64 (x0 : real) := real_sub x0 (real_of_num (NUMERAL 0)).
Definition term13 (x0 : real) := exists y0 : real, ((real_le y0 (real_add x0 y0)) /\ (~ (real_le (real_of_num (NUMERAL 0)) x0))) \/ ((~ (real_le y0 (real_add x0 y0))) /\ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term24 (x0 : real) (x1 : real) := real_sub (real_add x0 x1) x1.
Definition term130 (x0 : real) := fun y0 : real => (fun y1 : real => real_ge x0 (real_of_num (NUMERAL 0))) y0.
Definition term110 (x0 : real) := fun y0 : real => real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term86 (x0 : real) := fun y0 : real => (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term173 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term113 (x0 : real) := fun y0 : real => (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y1 : real => real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) y0).
Definition term15 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_le y2 (real_add y1 y2)) = (real_le (real_of_num (NUMERAL 0)) y1)) y0).
Definition term7 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_le y1 (real_add x0 y1)) = (real_le (real_of_num (NUMERAL 0)) x0)) y0).
Definition term65 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term52 (x0 : real) (x1 : real) := ~ (real_le x1 (real_add x0 x1)).
Definition term20 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_le y2 (real_add y1 y2)) = (real_le (real_of_num (NUMERAL 0)) y1)) y0).
Definition term73 (x0 : real) (x1 : real) := or ((real_le x0 (real_add x1 x0)) /\ (~ (real_le (real_of_num (NUMERAL 0)) x1))).
Definition term8 (x0 : real) := fun y0 : real => (real_le y0 (real_add x0 y0)) = (real_le (real_of_num (NUMERAL 0)) x0).
Definition term39 (x0 : real) (x1 : real) := real_ge (real_sub (real_add x0 x1) x1).
Definition term31 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term82 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term155 := (exists y0 : real, (real_ge y0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) \/ (exists y0 : real, (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))) /\ (real_ge y0 (real_of_num (NUMERAL 0)))).
Definition term103 (x0 : real) := (exists y0 : real, (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) \/ (exists y0 : real, (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))).
Definition term14 := ~ (forall y0 : real, forall y1 : real, (real_le y1 (real_add y0 y1)) = (real_le (real_of_num (NUMERAL 0)) y0)).
Definition term51 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term182 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term67 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term57 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term139 := fun y0 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))) /\ (real_ge y0 (real_of_num (NUMERAL 0))).
Definition term83 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term181 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term69 (x0 : real) (x1 : real) := and (~ (real_le x1 (real_add x0 x1))).
Definition term164 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term167 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term53 (x0 : real) (x1 : real) := real_gt (real_sub x1 (real_add x0 x1)) (real_of_num (NUMERAL 0)).
Definition term19 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_le y1 (real_add y0 y1)) = (real_le (real_of_num (NUMERAL 0)) y0)) x0).
Definition term78 := fun y0 : real => exists y1 : real, ((real_ge y0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))) /\ (real_ge y0 (real_of_num (NUMERAL 0)))).
Definition term21 := fun y0 : real => exists y1 : real, ((real_le y1 (real_add y0 y1)) /\ (~ (real_le (real_of_num (NUMERAL 0)) y0))) \/ ((~ (real_le y1 (real_add y0 y1))) /\ (real_le (real_of_num (NUMERAL 0)) y0)).
Definition term178 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term163 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term146 := @eq Prop (exists y0 : real, ((real_ge y0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))) /\ (real_ge y0 (real_of_num (NUMERAL 0))))).
Definition term145 := @eq Prop (exists y0 : real, ((fun y1 : real => (real_ge y1 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0) \/ ((fun y1 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0))) /\ (real_ge y1 (real_of_num (NUMERAL 0)))) y0)).
Definition term129 (x0 : real) := @eq Prop (exists y0 : real, (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))).
Definition term128 (x0 : real) := @eq Prop (exists y0 : real, (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((fun y1 : real => real_ge x0 (real_of_num (NUMERAL 0))) y0)).
Definition term115 (x0 : real) := @eq Prop (exists y0 : real, (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term114 (x0 : real) := @eq Prop (exists y0 : real, (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y1 : real => real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) y0)).
Definition term94 (x0 : real) := @eq Prop (exists y0 : real, ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))))).
Definition term93 (x0 : real) := @eq Prop (exists y0 : real, ((fun y1 : real => (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) y0) \/ ((fun y1 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) y0)).
Definition term174 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term16 := fun y0 : real => forall y1 : real, (real_le y1 (real_add y0 y1)) = (real_le (real_of_num (NUMERAL 0)) y0).
Definition term5 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term17 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y1 (real_add y0 y1)) = (real_le (real_of_num (NUMERAL 0)) y0)) x0.
Definition term0 (x0 : real) (x1 : real) := ~ ((real_le x0 (real_add x1 x0)) = (real_le (real_of_num (NUMERAL 0)) x1)).
Definition term158 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term161 := S (Nat.add 0 0).
Definition term29 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term3 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term30 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term183 := (~ (forall y0 : real, forall y1 : real, (real_le y1 (real_add y0 y1)) = (real_le (real_of_num (NUMERAL 0)) y0))) -> False.
Definition term138 := fun y0 : real => (real_ge y0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))).
Definition term70 (x0 : real) := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term126 (x0 : real) (x1 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => real_ge x0 (real_of_num (NUMERAL 0))) x1).
Definition term76 (x0 : real) := fun y0 : real => ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))).
Definition term62 (x0 : real) (x1 : real) := real_gt (real_sub x1 (real_add x0 x1)).
Definition term36 := real_mul (real_of_num (NUMERAL 0)).
Definition term46 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term27 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term120 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term43 (x0 : real) := real_sub (real_of_num (NUMERAL 0)) x0.
Definition term88 (x0 : real) (x1 : real) := (fun y0 : real => (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) x1.
Definition term144 := fun y0 : real => ((fun y1 : real => (real_ge y1 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0) \/ ((fun y1 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0))) /\ (real_ge y1 (real_of_num (NUMERAL 0)))) y0).
Definition term92 (x0 : real) := fun y0 : real => ((fun y1 : real => (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) y0) \/ ((fun y1 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) y0).
Definition term109 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ (exists y0 : real, (fun y1 : real => real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) y0).
Definition term142 (x0 : real) := (fun y0 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))) /\ (real_ge y0 (real_of_num (NUMERAL 0)))) x0.
Definition term136 := exists y0 : real, ((fun y1 : real => (real_ge y1 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0) \/ ((fun y1 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0))) /\ (real_ge y1 (real_of_num (NUMERAL 0)))) y0).
Definition term84 (x0 : real) := exists y0 : real, ((fun y1 : real => (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) y0) \/ ((fun y1 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) y0).
Definition term184 := ((~ (forall y0 : real, forall y1 : real, (real_le y1 (real_add y0 y1)) = (real_le (real_of_num (NUMERAL 0)) y0))) -> False) -> forall y0 : real, forall y1 : real, (real_le y1 (real_add y0 y1)) = (real_le (real_of_num (NUMERAL 0)) y0).
Definition term74 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term44 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term143 (x0 : real) := ((fun y0 : real => (real_ge y0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) x0) \/ ((fun y0 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))) /\ (real_ge y0 (real_of_num (NUMERAL 0)))) x0).
Definition term168 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term50 (x0 : real) (x1 : real) := (real_le x0 (real_add x1 x0)) /\ (~ (real_le (real_of_num (NUMERAL 0)) x1)).
Definition term89 (x0 : real) (x1 : real) := or ((fun y0 : real => (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) x1).
Definition term58 (x0 : real) (x1 : real) := real_add x1 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term165 := real_of_num (NUMERAL (BIT1 0)).
Definition term60 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term2 (x0 : real) (x1 : real) := real_le x1 (real_add x0 x1).
Definition term152 := fun y0 : real => (fun y1 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0))) /\ (real_ge y1 (real_of_num (NUMERAL 0)))) y0.
Definition term147 := fun y0 : real => (fun y1 : real => (real_ge y1 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0.
Definition term100 (x0 : real) := fun y0 : real => (fun y1 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) y0.
Definition term95 (x0 : real) := fun y0 : real => (fun y1 : real => (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) y0.
Definition term116 (x0 : real) := fun y0 : real => (fun y1 : real => real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) y0.
Definition term149 := exists y0 : real, (real_ge y0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))).
Definition term97 (x0 : real) := exists y0 : real, (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term91 (x0 : real) (x1 : real) := ((fun y0 : real => (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) x1) \/ ((fun y0 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) x1).
Definition term25 (x0 : real) (x1 : real) := real_add (real_add x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term37 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term75 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))).
Definition term179 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term177 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term127 (x0 : real) := fun y0 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((fun y1 : real => real_ge x0 (real_of_num (NUMERAL 0))) y0).
Definition term11 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_le y1 (real_add x0 y1)) = (real_le (real_of_num (NUMERAL 0)) x0)) y0).
Definition term135 := exists y0 : real, ((real_ge y0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))) /\ (real_ge y0 (real_of_num (NUMERAL 0)))).
Definition term77 (x0 : real) := exists y0 : real, ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))).
Definition term90 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) x1.
Definition term134 := fun y0 : real => ((real_ge y0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))) /\ (real_ge y0 (real_of_num (NUMERAL 0)))).
Definition term141 (x0 : real) := or ((fun y0 : real => (real_ge y0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) x0).
Definition term26 (x0 : real) (x1 : real) := real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term72 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term47 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term59 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term33 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term55 (x0 : real) (x1 : real) := real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1)).
Definition term48 (x0 : real) (x1 : real) := and (real_le x1 (real_add x0 x1)).
Definition term169 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term151 := or (exists y0 : real, (real_ge y0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))).
Definition term99 (x0 : real) := or (exists y0 : real, (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term68 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term112 (x0 : real) (x1 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((fun y0 : real => real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) x1).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term63 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term171 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term140 (x0 : real) := (fun y0 : real => (real_ge y0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) x0.
Definition term132 (x0 : real) := exists y0 : real, real_ge x0 (real_of_num (NUMERAL 0)).
Definition term119 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ (exists y0 : real, real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term34 := NUMERAL (BIT1 0).
Definition term137 := (exists y0 : real, (fun y1 : real => (real_ge y1 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0) \/ (exists y0 : real, (fun y1 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0))) /\ (real_ge y1 (real_of_num (NUMERAL 0)))) y0).
Definition term85 (x0 : real) := (exists y0 : real, (fun y1 : real => (real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) y0) \/ (exists y0 : real, (fun y1 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) y0).
Definition term175 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term170 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term28 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term159 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term180 := real_gt (real_of_num (NUMERAL 0)).
Definition term157 := @eq Prop ((exists y0 : real, (real_ge y0 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0)))) \/ (exists y0 : real, (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_of_num (NUMERAL 0))) /\ (real_ge y0 (real_of_num (NUMERAL 0))))).
Definition term156 := @eq Prop ((exists y0 : real, (fun y1 : real => (real_ge y1 (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0)))) y0) \/ (exists y0 : real, (fun y1 : real => (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_of_num (NUMERAL 0))) /\ (real_ge y1 (real_of_num (NUMERAL 0)))) y0)).
