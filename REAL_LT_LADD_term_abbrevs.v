Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term56 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term17 (x0 : real) (x1 : real) := forall y0 : real, (real_lt (real_add x0 x1) (real_add x0 y0)) = (real_lt x1 y0).
Definition term47 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term3 (x0 : real -> Prop) := ~ (all x0).
Definition term68 (x0 : real) (x1 : real) (x2 : real) := real_ge (real_sub (real_add x1 x0) (real_add x1 x2)) (real_of_num (NUMERAL 0)).
Definition term70 (x0 : real) (x1 : real) (x2 : real) := real_ge (real_sub (real_add x1 x0) (real_add x1 x2)).
Definition term133 := (exists y0 : real, exists y1 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) \/ (exists y0 : real, exists y1 : real, (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0)))).
Definition term98 (x0 : real) (x1 : real) := (fun y0 : real => (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0)))) x1.
Definition term44 := real_of_num (NUMERAL 0).
Definition term34 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1).
Definition term96 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) x1.
Definition term152 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term146 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term67 (x0 : real) (x1 : real) (x2 : real) := ~ (real_lt (real_add x1 x0) (real_add x1 x2)).
Definition term76 (x0 : real) (x1 : real) := (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term64 (x0 : real) (x1 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term5 (x0 : real) (x1 : real) := ~ (forall y0 : real, (real_lt (real_add x0 x1) (real_add x0 y0)) = (real_lt x1 y0)).
Definition term119 (x0 : real) := or ((fun y0 : real => exists y1 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) x0).
Definition term31 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub (real_add x1 x0) (real_add x1 x2)) (real_of_num (NUMERAL 0)).
Definition term73 (x0 : real) (x1 : real) (x2 : real) := and (~ (real_lt (real_add x1 x0) (real_add x1 x2))).
Definition term8 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_lt (real_add x0 x1) (real_add x0 y0)) = (real_lt x1 y0)) x2.
Definition term53 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term33 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x1 x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x1 x2)).
Definition term54 (x0 : real) (x1 : real) := real_add (real_of_num (NUMERAL 0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term38 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x1 x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)).
Definition term140 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term87 (x0 : Prop) := exists y0 : real, x0.
Definition term109 (x0 : real) := exists y0 : real, (fun y1 : real => (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0)))) y0.
Definition term104 (x0 : real) := exists y0 : real, (fun y1 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) y0.
Definition term169 := forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_add y0 y1) (real_add y0 y2)) = (real_lt y1 y2).
Definition term26 (x0 : real) := forall y0 : real, forall y1 : real, (real_lt (real_add x0 y0) (real_add x0 y1)) = (real_lt y0 y1).
Definition term161 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term2 (x0 : real) (x1 : real) (x2 : real) := real_lt (real_add x1 x0) (real_add x1 x2).
Definition term132 := exists y0 : real, exists y1 : real, (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))).
Definition term127 := exists y0 : real, exists y1 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))).
Definition term85 := exists y0 : real, exists y1 : real, exists y2 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0)))).
Definition term83 := exists y0 : real, exists y1 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0)))).
Definition term30 := exists y0 : real, exists y1 : real, exists y2 : real, ((real_lt (real_add y0 y1) (real_add y0 y2)) /\ (~ (real_lt y1 y2))) \/ ((~ (real_lt (real_add y0 y1) (real_add y0 y2))) /\ (real_lt y1 y2)).
Definition term21 (x0 : real) := exists y0 : real, exists y1 : real, ((real_lt (real_add x0 y0) (real_add x0 y1)) /\ (~ (real_lt y0 y1))) \/ ((~ (real_lt (real_add x0 y0) (real_add x0 y1))) /\ (real_lt y0 y1)).
Definition term128 := or (exists y0 : real, (fun y1 : real => exists y2 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0)))) y0).
Definition term106 (x0 : real) := or (exists y0 : real, (fun y1 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) y0).
Definition term147 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term12 (x0 : real) (x1 : real) := exists y0 : real, ((real_lt (real_add x0 x1) (real_add x0 y0)) /\ (~ (real_lt x1 y0))) \/ ((~ (real_lt (real_add x0 x1) (real_add x0 y0))) /\ (real_lt x1 y0)).
Definition term32 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_add x1 x0) (real_add x1 x2).
Definition term157 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term23 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, (real_lt (real_add y1 y2) (real_add y1 y3)) = (real_lt y2 y3)) y0).
Definition term14 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_lt (real_add x0 y1) (real_add x0 y2)) = (real_lt y1 y2)) y0).
Definition term6 (x0 : real) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => (real_lt (real_add x0 x1) (real_add x0 y1)) = (real_lt x1 y1)) y0).
Definition term120 (x0 : real) := (fun y0 : real => exists y1 : real, (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0)))) x0.
Definition term118 (x0 : real) := (fun y0 : real => exists y1 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) x0.
Definition term28 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, (real_lt (real_add y1 y2) (real_add y1 y3)) = (real_lt y2 y3)) y0).
Definition term19 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_lt (real_add x0 y1) (real_add x0 y2)) = (real_lt y1 y2)) y0).
Definition term37 (x0 : real) (x1 : real) := real_add (real_add x0 x1).
Definition term62 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term121 (x0 : real) := ((fun y0 : real => exists y1 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) x0) \/ ((fun y0 : real => exists y1 : real, (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0)))) x0).
Definition term43 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term94 (x0 : real) := fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))).
Definition term11 (x0 : real) (x1 : real) := fun y0 : real => ((real_lt (real_add x0 x1) (real_add x0 y0)) /\ (~ (real_lt x1 y0))) \/ ((~ (real_lt (real_add x0 x1) (real_add x0 y0))) /\ (real_lt x1 y0)).
Definition term90 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term111 (x0 : real) := (exists y0 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) \/ (exists y0 : real, (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0)))).
Definition term22 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_add y0 y1) (real_add y0 y2)) = (real_lt y1 y2)).
Definition term13 (x0 : real) := ~ (forall y0 : real, forall y1 : real, (real_lt (real_add x0 y0) (real_add x0 y1)) = (real_lt y0 y1)).
Definition term166 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term75 (x0 : real) (x1 : real) (x2 : real) := (~ (real_lt (real_add x0 x1) (real_add x0 x2))) /\ (real_lt x1 x2).
Definition term58 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term35 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term130 := fun y0 : real => (fun y1 : real => exists y2 : real, (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0)))) y0.
Definition term125 := fun y0 : real => (fun y1 : real => exists y2 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0)))) y0.
Definition term142 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term91 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term165 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term78 (x0 : real) (x1 : real) := or ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))).
Definition term65 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_add x0 x1) (real_add x0 x2)) /\ (~ (real_lt x1 x2)).
Definition term50 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term55 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub (real_add x1 x0) (real_add x1 x2)).
Definition term27 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, (real_lt (real_add y0 y1) (real_add y0 y2)) = (real_lt y1 y2)) x0).
Definition term117 := fun y0 : real => exists y1 : real, (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))).
Definition term116 := fun y0 : real => exists y1 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))).
Definition term82 := fun y0 : real => exists y1 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0)))).
Definition term20 (x0 : real) := fun y0 : real => exists y1 : real, ((real_lt (real_add x0 y0) (real_add x0 y1)) /\ (~ (real_lt y0 y1))) \/ ((~ (real_lt (real_add x0 y0) (real_add x0 y1))) /\ (real_lt y0 y1)).
Definition term160 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term143 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term124 := @eq Prop (exists y0 : real, (exists y1 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) \/ (exists y1 : real, (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))))).
Definition term123 := @eq Prop (exists y0 : real, ((fun y1 : real => exists y2 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0)))) y0) \/ ((fun y1 : real => exists y2 : real, (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0)))) y0)).
Definition term102 (x0 : real) := @eq Prop (exists y0 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))))).
Definition term101 (x0 : real) := @eq Prop (exists y0 : real, ((fun y1 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) y0) \/ ((fun y1 : real => (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0)))) y0)).
Definition term15 (x0 : real) := fun y0 : real => forall y1 : real, (real_lt (real_add x0 y0) (real_add x0 y1)) = (real_lt y0 y1).
Definition term4 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term95 (x0 : real) := fun y0 : real => (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))).
Definition term9 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (real_lt (real_add x0 x1) (real_add x0 y0)) = (real_lt x1 y0)) x2).
Definition term138 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term1 (x0 : real) (x1 : real) (x2 : real) := ((real_lt (real_add x0 x1) (real_add x0 x2)) /\ (~ (real_lt x1 x2))) \/ ((~ (real_lt (real_add x0 x1) (real_add x0 x2))) /\ (real_lt x1 x2)).
Definition term61 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term141 := S (Nat.add 0 0).
Definition term42 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term148 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term36 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term167 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_add y0 y1) (real_add y0 y2)) = (real_lt y1 y2))) -> False.
Definition term66 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term159 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term60 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1).
Definition term154 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term153 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term48 := real_mul (real_of_num (NUMERAL 0)).
Definition term16 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_lt (real_add x0 y0) (real_add x0 y1)) = (real_lt y0 y1)) x1.
Definition term40 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term86 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term77 (x0 : real) (x1 : real) (x2 : real) := or ((real_lt (real_add x0 x1) (real_add x0 x2)) /\ (~ (real_lt x1 x2))).
Definition term100 (x0 : real) := fun y0 : real => ((fun y1 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) y0) \/ ((fun y1 : real => (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0)))) y0).
Definition term114 := exists y0 : real, ((fun y1 : real => exists y2 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0)))) y0) \/ ((fun y1 : real => exists y2 : real, (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0)))) y0).
Definition term92 (x0 : real) := exists y0 : real, ((fun y1 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) y0) \/ ((fun y1 : real => (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0)))) y0).
Definition term144 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term168 := ((~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_add y0 y1) (real_add y0 y2)) = (real_lt y1 y2))) -> False) -> forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_add y0 y1) (real_add y0 y2)) = (real_lt y1 y2).
Definition term71 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term24 := fun y0 : real => forall y1 : real, forall y2 : real, (real_lt (real_add y0 y1) (real_add y0 y2)) = (real_lt y1 y2).
Definition term18 (x0 : real) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, (real_lt (real_add x0 y0) (real_add x0 y1)) = (real_lt y0 y1)) x1).
Definition term84 := fun y0 : real => exists y1 : real, exists y2 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0)))).
Definition term29 := fun y0 : real => exists y1 : real, exists y2 : real, ((real_lt (real_add y0 y1) (real_add y0 y2)) /\ (~ (real_lt y1 y2))) \/ ((~ (real_lt (real_add y0 y1) (real_add y0 y2))) /\ (real_lt y1 y2)).
Definition term69 (x0 : real) (x1 : real) := real_add (real_of_num (NUMERAL 0)) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term97 (x0 : real) (x1 : real) := or ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) x1).
Definition term145 := real_of_num (NUMERAL (BIT1 0)).
Definition term108 (x0 : real) := fun y0 : real => (fun y1 : real => (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0)))) y0.
Definition term103 (x0 : real) := fun y0 : real => (fun y1 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) y0.
Definition term63 (x0 : real) (x1 : real) (x2 : real) := and (real_lt (real_add x1 x0) (real_add x1 x2)).
Definition term110 (x0 : real) := exists y0 : real, (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))).
Definition term105 (x0 : real) := exists y0 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))).
Definition term99 (x0 : real) (x1 : real) := ((fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) x1) \/ ((fun y0 : real => (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0)))) x1).
Definition term49 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term10 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (real_lt (real_add x0 x1) (real_add x0 y1)) = (real_lt x1 y1)) y0).
Definition term81 (x0 : real) := exists y0 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0)))).
Definition term7 (x0 : real) (x1 : real) := fun y0 : real => (real_lt (real_add x0 x1) (real_add x0 y0)) = (real_lt x1 y0).
Definition term74 (x0 : real) (x1 : real) := and (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term0 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_lt (real_add x0 x1) (real_add x0 x2)) = (real_lt x1 x2)).
Definition term162 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term80 (x0 : real) := fun y0 : real => ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0)))).
Definition term163 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term52 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term45 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term39 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)).
Definition term113 := exists y0 : real, (exists y1 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) \/ (exists y1 : real, (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0)))).
Definition term156 (x0 : real) (x1 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term122 := fun y0 : real => ((fun y1 : real => exists y2 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0)))) y0) \/ ((fun y1 : real => exists y2 : real, (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0)))) y0).
Definition term72 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1).
Definition term51 := real_add (real_of_num (NUMERAL 0)).
Definition term107 (x0 : real) := or (exists y0 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))).
Definition term158 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term79 (x0 : real) (x1 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))).
Definition term25 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_lt (real_add y0 y1) (real_add y0 y2)) = (real_lt y1 y2)) x0.
Definition term129 := or (exists y0 : real, exists y1 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term151 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term57 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term112 := fun y0 : real => (exists y1 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) \/ (exists y1 : real, (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0)))).
Definition term46 := NUMERAL (BIT1 0).
Definition term115 := (exists y0 : real, (fun y1 : real => exists y2 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0)))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0)))) y0).
Definition term93 (x0 : real) := (exists y0 : real, (fun y1 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) y0) \/ (exists y0 : real, (fun y1 : real => (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0)))) y0).
Definition term155 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term150 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term41 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term139 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term131 := exists y0 : real, (fun y1 : real => exists y2 : real, (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0)))) y0.
Definition term126 := exists y0 : real, (fun y1 : real => exists y2 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0)))) y0.
Definition term149 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term59 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term164 := real_gt (real_of_num (NUMERAL 0)).
Definition term137 (x0 : real) := @eq Prop ((exists y0 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0)))) \/ (exists y0 : real, (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))))).
Definition term136 (x0 : real) := @eq Prop ((exists y0 : real, (fun y1 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) y0) \/ (exists y0 : real, (fun y1 : real => (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0)))) y0)).
Definition term135 := @eq Prop ((exists y0 : real, exists y1 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0)))) \/ (exists y0 : real, exists y1 : real, (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))))).
Definition term134 := @eq Prop ((exists y0 : real, (fun y1 : real => exists y2 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0)))) y0) \/ (exists y0 : real, (fun y1 : real => exists y2 : real, (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0)))) y0)).