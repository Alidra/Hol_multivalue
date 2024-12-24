Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term96 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2).
Definition term132 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term4 (x0 : real -> Prop) := ~ (all x0).
Definition term90 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term36 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x1 x2))).
Definition term39 := real_of_num (NUMERAL 0).
Definition term45 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1).
Definition term3 (x0 : real) (x1 : real) (x2 : real) := real_lt x0 (real_add x1 x2).
Definition term49 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)).
Definition term98 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)).
Definition term42 (x0 : real) (x1 : real) (x2 : real) := real_ge (real_sub x0 (real_add x1 x2)) (real_of_num (NUMERAL 0)).
Definition term14 (x0 : real) (x1 : real) := exists y0 : real, (real_lt (real_abs (real_sub x1 x0)) y0) /\ (~ (real_lt x0 (real_add x1 y0))).
Definition term110 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))).
Definition term138 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1).
Definition term6 (x0 : real) (x1 : real) := ~ (forall y0 : real, (real_lt (real_abs (real_sub x1 x0)) y0) -> real_lt x0 (real_add x1 y0)).
Definition term80 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_sub x0 x1).
Definition term137 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term44 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x1 x2)).
Definition term141 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2))).
Definition term52 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term76 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))).
Definition term68 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) x2) /\ (real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x1)) x2).
Definition term108 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term73 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_sub x1 x2)).
Definition term19 (x0 : real) (x1 : real) := forall y0 : real, (real_lt (real_abs (real_sub x1 x0)) y0) -> real_lt x0 (real_add x1 y0).
Definition term147 := forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_abs (real_sub y0 y1)) y2) -> real_lt y1 (real_add y0 y2).
Definition term28 (x0 : real) := forall y0 : real, forall y1 : real, (real_lt (real_abs (real_sub x0 y0)) y1) -> real_lt y0 (real_add x0 y1).
Definition term58 (x0 : real) (x1 : real) (x2 : real) := and (real_lt (real_abs (real_sub x0 x1)) x2).
Definition term83 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term40 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x1 x2)))) (real_of_num (NUMERAL 0)).
Definition term66 := exists y0 : real, exists y1 : real, exists y2 : real, (real_gt (real_add y2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub y0 y1)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1)) (real_of_num (NUMERAL 0))).
Definition term64 (x0 : real) := exists y0 : real, exists y1 : real, (real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x0 y0)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0)) (real_of_num (NUMERAL 0))).
Definition term32 := exists y0 : real, exists y1 : real, exists y2 : real, (real_lt (real_abs (real_sub y0 y1)) y2) /\ (~ (real_lt y1 (real_add y0 y2))).
Definition term23 (x0 : real) := exists y0 : real, exists y1 : real, (real_lt (real_abs (real_sub x0 y0)) y1) /\ (~ (real_lt y0 (real_add x0 y1))).
Definition term125 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2))) (real_of_num (NUMERAL 0)).
Definition term87 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term103 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))).
Definition term69 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_sub x1 x2))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_sub x1 x2))) (real_of_num (NUMERAL 0))).
Definition term72 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term67 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x1))) x2.
Definition term25 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, (real_lt (real_abs (real_sub y1 y2)) y3) -> real_lt y2 (real_add y1 y3)) y0).
Definition term16 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_lt (real_abs (real_sub x0 y1)) y2) -> real_lt y1 (real_add x0 y2)) y0).
Definition term7 (x0 : real) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => (real_lt (real_abs (real_sub x1 x0)) y1) -> real_lt x0 (real_add x1 y1)) y0).
Definition term126 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)).
Definition term30 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, (real_lt (real_abs (real_sub y1 y2)) y3) -> real_lt y2 (real_add y1 y3)) y0).
Definition term21 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_lt (real_abs (real_sub x0 y1)) y2) -> real_lt y1 (real_add x0 y2)) y0).
Definition term22 (x0 : real) := fun y0 : real => exists y1 : real, (real_lt (real_abs (real_sub x0 y0)) y1) /\ (~ (real_lt y0 (real_add x0 y1))).
Definition term17 (x0 : real) := fun y0 : real => forall y1 : real, (real_lt (real_abs (real_sub x0 y0)) y1) -> real_lt y0 (real_add x0 y1).
Definition term116 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))).
Definition term130 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term91 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term24 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_abs (real_sub y0 y1)) y2) -> real_lt y1 (real_add y0 y2)).
Definition term15 (x0 : real) := ~ (forall y0 : real, forall y1 : real, (real_lt (real_abs (real_sub x0 y0)) y1) -> real_lt y0 (real_add x0 y1)).
Definition term74 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)).
Definition term144 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term119 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)))) (real_of_num (NUMERAL 0)).
Definition term46 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term54 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2).
Definition term143 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term33 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub x0 (real_abs (real_sub x1 x2))) (real_of_num (NUMERAL 0)).
Definition term94 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term135 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term29 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, (real_lt (real_abs (real_sub y0 y1)) y2) -> real_lt y1 (real_add y0 y2)) x0).
Definition term63 (x0 : real) := fun y0 : real => exists y1 : real, (real_gt (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x0 y0)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0)) (real_of_num (NUMERAL 0))).
Definition term102 (x0 : real) (x1 : real) (x2 : real) := and (real_gt (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))).
Definition term55 (x0 : real) (x1 : real) (x2 : real) := real_ge (real_sub x0 (real_add x1 x2)).
Definition term139 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term35 (x0 : real) (x1 : real) (x2 : real) := real_sub x0 (real_abs (real_sub x1 x2)).
Definition term61 (x0 : real) (x1 : real) := fun y0 : real => (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x0 x1)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0))).
Definition term93 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term111 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term10 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_abs (real_sub x1 x0)) x2) -> real_lt x0 (real_add x1 x2).
Definition term71 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_sub x0 x1).
Definition term5 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term11 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (real_lt (real_abs (real_sub x1 x0)) y0) -> real_lt x0 (real_add x1 y0)) x2).
Definition term121 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)))).
Definition term105 (x0 : real) (x1 : real) (x2 : real) := ((real_gt (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))).
Definition term106 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term109 := S (Nat.add 0 0).
Definition term79 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term129 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term47 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term104 (x0 : real) (x1 : real) (x2 : real) := and ((real_gt (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0)))).
Definition term145 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_abs (real_sub y0 y1)) y2) -> real_lt y1 (real_add y0 y2))) -> False.
Definition term57 (x0 : real) (x1 : real) (x2 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0)).
Definition term34 (x0 : real) (x1 : real) := real_abs (real_sub x0 x1).
Definition term133 := real_mul (real_of_num (NUMERAL 0)).
Definition term43 (x0 : real) (x1 : real) (x2 : real) := real_sub x0 (real_add x1 x2).
Definition term18 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_lt (real_abs (real_sub x0 y0)) y1) -> real_lt y0 (real_add x0 y1)) x1.
Definition term50 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term70 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term9 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_lt (real_abs (real_sub x1 x0)) y0) -> real_lt x0 (real_add x1 y0)) x2.
Definition term112 (x0 : real) (x1 : real) (x2 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2))) (real_of_num (NUMERAL 0)).
Definition term146 := ((~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_abs (real_sub y0 y1)) y2) -> real_lt y1 (real_add y0 y2))) -> False) -> forall y0 : real, forall y1 : real, forall y2 : real, (real_lt (real_abs (real_sub y0 y1)) y2) -> real_lt y1 (real_add y0 y2).
Definition term115 (x0 : real) (x1 : real) (x2 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2))).
Definition term85 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term8 (x0 : real) (x1 : real) := fun y0 : real => (real_lt (real_abs (real_sub x1 x0)) y0) -> real_lt x0 (real_add x1 y0).
Definition term26 := fun y0 : real => forall y1 : real, forall y2 : real, (real_lt (real_abs (real_sub y0 y1)) y2) -> real_lt y1 (real_add y0 y2).
Definition term20 (x0 : real) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, (real_lt (real_abs (real_sub x0 y0)) y1) -> real_lt y0 (real_add x0 y1)) x1).
Definition term65 := fun y0 : real => exists y1 : real, exists y2 : real, (real_gt (real_add y2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub y0 y1)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1)) (real_of_num (NUMERAL 0))).
Definition term31 := fun y0 : real => exists y1 : real, exists y2 : real, (real_lt (real_abs (real_sub y0 y1)) y2) /\ (~ (real_lt y1 (real_add y0 y2))).
Definition term95 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_sub x1 x2)).
Definition term97 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_sub x1 x2))).
Definition term75 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_sub x1 x2))).
Definition term88 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term92 := real_of_num (NUMERAL (BIT1 0)).
Definition term53 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term62 (x0 : real) (x1 : real) := exists y0 : real, (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x0 x1)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0))).
Definition term134 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term84 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term13 (x0 : real) (x1 : real) := fun y0 : real => (real_lt (real_abs (real_sub x1 x0)) y0) /\ (~ (real_lt x0 (real_add x1 y0))).
Definition term12 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (real_lt (real_abs (real_sub x1 x0)) y1) -> real_lt x0 (real_add x1 y1)) y0).
Definition term1 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_abs (real_sub x1 x0)) x2) /\ (~ (real_lt x0 (real_add x1 x2))).
Definition term41 (x0 : real) (x1 : real) (x2 : real) := ~ (real_lt x0 (real_add x1 x2)).
Definition term127 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)).
Definition term86 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term37 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub x0 (real_abs (real_sub x1 x2))).
Definition term140 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term100 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0)).
Definition term81 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term51 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term120 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))).
Definition term131 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term78 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0)).
Definition term124 (x0 : real) (x1 : real) (x2 : real) := ((real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2))) (real_of_num (NUMERAL 0)).
Definition term118 (x0 : real) (x1 : real) (x2 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)))) (real_of_num (NUMERAL 0)).
Definition term136 := real_add (real_of_num (NUMERAL 0)).
Definition term27 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_lt (real_abs (real_sub y0 y1)) y2) -> real_lt y1 (real_add y0 y2)) x0.
Definition term122 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))).
Definition term60 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x1 x2)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)) (real_of_num (NUMERAL 0))).
Definition term38 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x1 x2)))).
Definition term56 (x0 : real) (x1 : real) (x2 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)).
Definition term0 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_lt (real_abs (real_sub x1 x0)) x2) -> real_lt x0 (real_add x1 x2)).
Definition term82 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term113 (x0 : real) (x1 : real) (x2 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2))) (real_of_num (NUMERAL 0)).
Definition term89 := NUMERAL (BIT1 0).
Definition term2 (x0 : real) (x1 : real) (x2 : real) := real_lt (real_abs (real_sub x0 x1)) x2.
Definition term114 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)).
Definition term123 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term117 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term128 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term107 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term101 (x0 : real) (x1 : real) (x2 : real) := and (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_sub x1 x2))) (real_of_num (NUMERAL 0))).
Definition term59 (x0 : real) (x1 : real) (x2 : real) := and (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x1 x2)))) (real_of_num (NUMERAL 0))).
Definition term99 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_sub x1 x2))) (real_of_num (NUMERAL 0)).
Definition term77 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_sub x1 x2))) (real_of_num (NUMERAL 0)).
Definition term142 := real_gt (real_of_num (NUMERAL 0)).
Definition term48 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)).
