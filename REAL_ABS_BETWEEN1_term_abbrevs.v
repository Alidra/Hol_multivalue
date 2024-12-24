Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term37 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term77 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2).
Definition term131 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term45 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_sub x0 x2) (real_abs (real_sub x1 x2)).
Definition term3 (x0 : real -> Prop) := ~ (all x0).
Definition term116 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term86 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term38 := real_of_num (NUMERAL 0).
Definition term157 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term151 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term40 (x0 : real) (x1 : real) (x2 : real) := real_lt (real_abs (real_sub x0 x2)) (real_sub x1 x2).
Definition term54 (x0 : real) (x1 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term5 (x0 : real) (x1 : real) := ~ (forall y0 : real, ((real_lt x0 y0) /\ (real_lt (real_abs (real_sub x1 x0)) (real_sub y0 x0))) -> real_lt x1 y0).
Definition term109 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term107 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_sub x0 x1).
Definition term47 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x1 x2))).
Definition term84 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term1 (x0 : real) (x1 : real) (x2 : real) := ((real_lt x0 x2) /\ (real_lt (real_abs (real_sub x1 x0)) (real_sub x2 x0))) /\ (~ (real_lt x1 x2)).
Definition term108 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term34 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term140 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_add x1 x2)) (real_of_num (NUMERAL 0))).
Definition term136 (x0 : real) (x1 : real) := real_add (real_of_num (NUMERAL 0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term121 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term143 (x0 : real) (x1 : real) (x2 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x2) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_add x1 x2)) (real_of_num (NUMERAL 0))))) /\ (real_ge (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)) (real_of_num (NUMERAL 0))).
Definition term146 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term76 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_sub x1 x2)).
Definition term173 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y2) /\ (real_lt (real_abs (real_sub y1 y0)) (real_sub y2 y0))) -> real_lt y1 y2.
Definition term27 (x0 : real) := forall y0 : real, forall y1 : real, ((real_lt x0 y1) /\ (real_lt (real_abs (real_sub y0 x0)) (real_sub y1 x0))) -> real_lt y0 y1.
Definition term110 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term134 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term69 := exists y0 : real, exists y1 : real, exists y2 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y2) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_add y2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub y1 y0))))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0))).
Definition term67 (x0 : real) := exists y0 : real, exists y1 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub y0 x0))))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))).
Definition term31 := exists y0 : real, exists y1 : real, exists y2 : real, ((real_lt y0 y2) /\ (real_lt (real_abs (real_sub y1 y0)) (real_sub y2 y0))) /\ (~ (real_lt y1 y2)).
Definition term22 (x0 : real) := exists y0 : real, exists y1 : real, ((real_lt x0 y1) /\ (real_lt (real_abs (real_sub y0 x0)) (real_sub y1 x0))) /\ (~ (real_lt y0 y1)).
Definition term114 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term12 (x0 : real) (x1 : real) := fun y0 : real => ((real_lt x0 y0) /\ (real_lt (real_abs (real_sub x1 x0)) (real_sub y0 x0))) /\ (~ (real_lt x1 y0)).
Definition term152 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term91 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term162 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term24 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, ((real_lt y1 y3) /\ (real_lt (real_abs (real_sub y2 y1)) (real_sub y3 y1))) -> real_lt y2 y3) y0).
Definition term15 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, ((real_lt x0 y2) /\ (real_lt (real_abs (real_sub y1 x0)) (real_sub y2 x0))) -> real_lt y1 y2) y0).
Definition term6 (x0 : real) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => ((real_lt x0 y1) /\ (real_lt (real_abs (real_sub x1 x0)) (real_sub y1 x0))) -> real_lt x1 y1) y0).
Definition term105 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_add x1 x2)) (real_of_num (NUMERAL 0)).
Definition term71 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) x3) /\ (real_gt (real_add x0 (real_add x1 (real_mul (real_of_num (NUMERAL (BIT1 0))) x2))) x3).
Definition term53 (x0 : real) (x1 : real) := and (real_lt x0 x1).
Definition term29 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, ((real_lt y1 y3) /\ (real_lt (real_abs (real_sub y2 y1)) (real_sub y3 y1))) -> real_lt y2 y3) y0).
Definition term20 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, ((real_lt x0 y2) /\ (real_lt (real_abs (real_sub y1 x0)) (real_sub y2 x0))) -> real_lt y1 y2) y0).
Definition term138 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_sub x1 x2)))) (real_of_num (NUMERAL 0)).
Definition term104 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_sub x1 x2)))) (real_of_num (NUMERAL 0)).
Definition term52 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x1 x2))))) (real_of_num (NUMERAL 0)).
Definition term21 (x0 : real) := fun y0 : real => exists y1 : real, ((real_lt x0 y1) /\ (real_lt (real_abs (real_sub y0 x0)) (real_sub y1 x0))) /\ (~ (real_lt y0 y1)).
Definition term87 := real_neg (real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term60 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term124 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_sub x1 x2))).
Definition term80 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_sub x1 x2))).
Definition term129 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term117 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term23 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y2) /\ (real_lt (real_abs (real_sub y1 y0)) (real_sub y2 y0))) -> real_lt y1 y2).
Definition term14 (x0 : real) := ~ (forall y0 : real, forall y1 : real, ((real_lt x0 y1) /\ (real_lt (real_abs (real_sub y0 x0)) (real_sub y1 x0))) -> real_lt y0 y1).
Definition term137 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_sub x1 x2)))).
Definition term102 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_sub x1 x2)))).
Definition term51 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x1 x2))))).
Definition term123 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)).
Definition term170 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term56 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term49 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x0 x1)).
Definition term13 (x0 : real) (x1 : real) := exists y0 : real, ((real_lt x0 y0) /\ (real_lt (real_abs (real_sub x1 x0)) (real_sub y0 x0))) /\ (~ (real_lt x1 y0)).
Definition term148 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term41 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub (real_sub x0 x2) (real_abs (real_sub x1 x2))) (real_of_num (NUMERAL 0)).
Definition term99 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term169 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term95 := real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term120 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term28 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt y0 y2) /\ (real_lt (real_abs (real_sub y1 y0)) (real_sub y2 y0))) -> real_lt y1 y2) x0).
Definition term66 (x0 : real) := fun y0 : real => exists y1 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub y0 x0))))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))).
Definition term127 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term141 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x2) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_add x1 x2)) (real_of_num (NUMERAL 0)))).
Definition term119 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term149 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term55 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x1 x2))))) (real_of_num (NUMERAL 0))).
Definition term46 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) x0) (real_abs (real_sub x1 x2)).
Definition term103 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_add x1 x2)).
Definition term2 (x0 : real) (x1 : real) (x2 : real) := (real_lt x2 x1) /\ (real_lt (real_abs (real_sub x0 x2)) (real_sub x1 x2)).
Definition term74 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_sub x0 x1).
Definition term16 (x0 : real) := fun y0 : real => forall y1 : real, ((real_lt x0 y1) /\ (real_lt (real_abs (real_sub y0 x0)) (real_sub y1 x0))) -> real_lt y0 y1.
Definition term4 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term101 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_add x1 x2).
Definition term78 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 x2).
Definition term10 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => ((real_lt x0 y0) /\ (real_lt (real_abs (real_sub x1 x0)) (real_sub y0 x0))) -> real_lt x1 y0) x2).
Definition term96 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term144 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term59 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term147 := S (Nat.add 0 0).
Definition term106 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term97 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term128 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term153 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term85 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term62 (x0 : real) (x1 : real) (x2 : real) := and ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x1 x2))))) (real_of_num (NUMERAL 0)))).
Definition term171 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y2) /\ (real_lt (real_abs (real_sub y1 y0)) (real_sub y2 y0))) -> real_lt y1 y2)) -> False.
Definition term159 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term94 := real_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term9 (x0 : real) (x1 : real) (x2 : real) := ((real_lt x0 x2) /\ (real_lt (real_abs (real_sub x1 x0)) (real_sub x2 x0))) -> real_lt x1 x2.
Definition term164 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term44 (x0 : real) (x1 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term0 (x0 : real) (x1 : real) (x2 : real) := ~ (((real_lt x0 x2) /\ (real_lt (real_abs (real_sub x1 x0)) (real_sub x2 x0))) -> real_lt x1 x2).
Definition term58 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1).
Definition term81 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 x2)).
Definition term158 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term42 (x0 : real) (x1 : real) := real_abs (real_sub x0 x1).
Definition term75 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term132 := real_mul (real_of_num (NUMERAL 0)).
Definition term17 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_lt x0 y1) /\ (real_lt (real_abs (real_sub y0 x0)) (real_sub y1 x0))) -> real_lt y0 y1) x1.
Definition term98 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0.
Definition term35 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term92 := NUMERAL (BIT0 (BIT1 0)).
Definition term125 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2)).
Definition term73 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term70 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_gt (real_add x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x2)))) x3.
Definition term72 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_sub x1 x2)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_sub x1 x2)))) (real_of_num (NUMERAL 0))).
Definition term150 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term172 := ((~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y2) /\ (real_lt (real_abs (real_sub y1 y0)) (real_sub y2 y0))) -> real_lt y1 y2)) -> False) -> forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y2) /\ (real_lt (real_abs (real_sub y1 y0)) (real_sub y2 y0))) -> real_lt y1 y2.
Definition term89 := Nat.add (BIT1 0) (BIT1 0).
Definition term32 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term112 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term64 (x0 : real) (x1 : real) := fun y0 : real => ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x1 x0))))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))).
Definition term25 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt y0 y2) /\ (real_lt (real_abs (real_sub y1 y0)) (real_sub y2 y0))) -> real_lt y1 y2.
Definition term19 (x0 : real) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, ((real_lt x0 y1) /\ (real_lt (real_abs (real_sub y0 x0)) (real_sub y1 x0))) -> real_lt y0 y1) x1).
Definition term68 := fun y0 : real => exists y1 : real, exists y2 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y2) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_add y2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub y1 y0))))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)) (real_of_num (NUMERAL 0))).
Definition term30 := fun y0 : real => exists y1 : real, exists y2 : real, ((real_lt y0 y2) /\ (real_lt (real_abs (real_sub y1 y0)) (real_sub y2 y0))) /\ (~ (real_lt y1 y2)).
Definition term7 (x0 : real) (x1 : real) := fun y0 : real => ((real_lt x0 y0) /\ (real_lt (real_abs (real_sub x1 x0)) (real_sub y0 x0))) -> real_lt x1 y0.
Definition term122 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_sub x1 x2)).
Definition term50 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub (real_sub x0 x2) (real_abs (real_sub x1 x2))).
Definition term115 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term118 := real_of_num (NUMERAL (BIT1 0)).
Definition term18 (x0 : real) (x1 : real) := forall y0 : real, ((real_lt x0 y0) /\ (real_lt (real_abs (real_sub x1 x0)) (real_sub y0 x0))) -> real_lt x1 y0.
Definition term100 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term79 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term90 := BIT0 (BIT1 0).
Definition term65 (x0 : real) (x1 : real) := exists y0 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x1 x0))))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))).
Definition term133 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term111 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term142 (x0 : real) (x1 : real) (x2 : real) := and ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x2) (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_add x1 x2)) (real_of_num (NUMERAL 0))))).
Definition term11 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => ((real_lt x0 y1) /\ (real_lt (real_abs (real_sub x1 x0)) (real_sub y1 x0))) -> real_lt x1 y1) y0).
Definition term83 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term93 := real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term82 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add x1 x2).
Definition term113 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term166 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term139 (x0 : real) (x1 : real) (x2 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_sub x1 x2)))) (real_of_num (NUMERAL 0))).
Definition term8 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_lt x0 y0) /\ (real_lt (real_abs (real_sub x1 x0)) (real_sub y0 x0))) -> real_lt x1 y0) x2.
Definition term167 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term43 (x0 : real) (x1 : real) := real_sub (real_sub x0 x1).
Definition term126 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x2).
Definition term48 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x1 x2)))).
Definition term33 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term63 (x0 : real) (x1 : real) (x2 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x2) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_sub x1 x0))))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)) (real_of_num (NUMERAL 0))).
Definition term61 (x0 : real) (x1 : real) (x2 : real) := and ((real_lt x2 x1) /\ (real_lt (real_abs (real_sub x0 x2)) (real_sub x1 x2))).
Definition term130 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term161 (x0 : real) (x1 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term36 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1).
Definition term135 := real_add (real_of_num (NUMERAL 0)).
Definition term163 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term26 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt y0 y2) /\ (real_lt (real_abs (real_sub y1 y0)) (real_sub y2 y0))) -> real_lt y1 y2) x0.
Definition term156 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term39 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term88 := NUMERAL (BIT1 0).
Definition term160 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term155 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term165 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term145 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term154 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term57 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term168 := real_gt (real_of_num (NUMERAL 0)).
