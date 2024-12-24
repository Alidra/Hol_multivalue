Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term47 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term116 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term4 (x0 : real -> Prop) := ~ (all x0).
Definition term48 := real_of_num (NUMERAL 0).
Definition term61 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1).
Definition term8 (x0 : real) (x1 : real) (x2 : real) := fun y0 : real => ((real_lt x0 x2) /\ (real_le x1 y0)) -> real_lt (real_add x0 x1) (real_add x2 y0).
Definition term89 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term68 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)).
Definition term99 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))).
Definition term104 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term93 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term138 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1).
Definition term55 (x0 : real) (x1 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term6 (x0 : real) (x1 : real) (x2 : real) := ~ (forall y0 : real, ((real_lt x0 x2) /\ (real_le x1 y0)) -> real_lt (real_add x0 x1) (real_add x2 y0)).
Definition term137 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term110 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))).
Definition term140 (x0 : real) (x1 : real) := real_gt (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term128 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term58 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_ge (real_sub (real_add x0 x1) (real_add x2 x3)) (real_of_num (NUMERAL 0)).
Definition term53 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term44 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term131 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term20 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => forall y1 : real, ((real_lt x0 x1) /\ (real_le y0 y1)) -> real_lt (real_add x0 y0) (real_add x1 y1)) x2).
Definition term65 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_add x0 x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)).
Definition term86 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term146 := forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y0 y1) /\ (real_le y2 y3)) -> real_lt (real_add y0 y2) (real_add y1 y3).
Definition term37 (x0 : real) := forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt x0 y0) /\ (real_le y1 y2)) -> real_lt (real_add x0 y1) (real_add y0 y2).
Definition term28 (x0 : real) (x1 : real) := forall y0 : real, forall y1 : real, ((real_lt x0 x1) /\ (real_le y0 y1)) -> real_lt (real_add x0 y0) (real_add x1 y1).
Definition term119 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term83 := exists y0 : real, exists y1 : real, exists y2 : real, exists y3 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2) y3) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_add y2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y3)))) (real_of_num (NUMERAL 0))).
Definition term81 (x0 : real) := exists y0 : real, exists y1 : real, exists y2 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)))) (real_of_num (NUMERAL 0))).
Definition term79 (x0 : real) (x1 : real) := exists y0 : real, exists y1 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)))) (real_of_num (NUMERAL 0))).
Definition term41 := exists y0 : real, exists y1 : real, exists y2 : real, exists y3 : real, ((real_lt y0 y1) /\ (real_le y2 y3)) /\ (~ (real_lt (real_add y0 y2) (real_add y1 y3))).
Definition term32 (x0 : real) := exists y0 : real, exists y1 : real, exists y2 : real, ((real_lt x0 y0) /\ (real_le y1 y2)) /\ (~ (real_lt (real_add x0 y1) (real_add y0 y2))).
Definition term23 (x0 : real) (x1 : real) := exists y0 : real, exists y1 : real, ((real_lt x0 x1) /\ (real_le y0 y1)) /\ (~ (real_lt (real_add x0 y0) (real_add x1 y1))).
Definition term106 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))) (real_of_num (NUMERAL 0))).
Definition term132 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term73 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := and ((real_lt x0 x1) /\ (real_le x2 x3)).
Definition term19 (x0 : real) (x1 : real) (x2 : real) := forall y0 : real, ((real_lt x0 x2) /\ (real_le x1 y0)) -> real_lt (real_add x0 x1) (real_add x2 y0).
Definition term34 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, forall y4 : real, ((real_lt y1 y2) /\ (real_le y3 y4)) -> real_lt (real_add y1 y3) (real_add y2 y4)) y0).
Definition term25 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, ((real_lt x0 y1) /\ (real_le y2 y3)) -> real_lt (real_add x0 y2) (real_add y1 y3)) y0).
Definition term16 (x0 : real) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, ((real_lt x0 x1) /\ (real_le y1 y2)) -> real_lt (real_add x0 y1) (real_add x1 y2)) y0).
Definition term7 (x0 : real) (x1 : real) (x2 : real) := exists y0 : real, ~ ((fun y1 : real => ((real_lt x0 x2) /\ (real_le x1 y1)) -> real_lt (real_add x0 x1) (real_add x2 y1)) y0).
Definition term121 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))).
Definition term54 (x0 : real) (x1 : real) := and (real_lt x0 x1).
Definition term127 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term52 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term39 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, forall y4 : real, ((real_lt y1 y2) /\ (real_le y3 y4)) -> real_lt (real_add y1 y3) (real_add y2 y4)) y0).
Definition term30 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, ((real_lt x0 y1) /\ (real_le y2 y3)) -> real_lt (real_add x0 y2) (real_add y1 y3)) y0).
Definition term21 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, ((real_lt x0 x1) /\ (real_le y1 y2)) -> real_lt (real_add x0 y1) (real_add x1 y2)) y0).
Definition term109 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3))))) (real_of_num (NUMERAL 0)).
Definition term111 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_add x1 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))).
Definition term64 (x0 : real) (x1 : real) := real_add (real_add x0 x1).
Definition term22 (x0 : real) (x1 : real) := fun y0 : real => exists y1 : real, ((real_lt x0 x1) /\ (real_le y0 y1)) /\ (~ (real_lt (real_add x0 y0) (real_add x1 y1))).
Definition term17 (x0 : real) (x1 : real) := fun y0 : real => forall y1 : real, ((real_lt x0 x1) /\ (real_le y0 y1)) -> real_lt (real_add x0 y0) (real_add x1 y1).
Definition term114 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term33 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y0 y1) /\ (real_le y2 y3)) -> real_lt (real_add y0 y2) (real_add y1 y3)).
Definition term24 (x0 : real) := ~ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt x0 y0) /\ (real_le y1 y2)) -> real_lt (real_add x0 y1) (real_add y0 y2)).
Definition term15 (x0 : real) (x1 : real) := ~ (forall y0 : real, forall y1 : real, ((real_lt x0 x1) /\ (real_le y0 y1)) -> real_lt (real_add x0 y0) (real_add x1 y1)).
Definition term143 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term62 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term142 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term60 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_add x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x2 x3)).
Definition term96 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))) (real_of_num (NUMERAL 0))).
Definition term124 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term98 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3))))) (real_of_num (NUMERAL 0)).
Definition term38 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y0 y1) /\ (real_le y2 y3)) -> real_lt (real_add y0 y2) (real_add y1 y3)) x0).
Definition term78 (x0 : real) (x1 : real) := fun y0 : real => exists y1 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)))) (real_of_num (NUMERAL 0))).
Definition term112 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term57 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ (real_lt (real_add x0 x1) (real_add x2 x3)).
Definition term90 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term136 (x0 : real) (x1 : real) := real_gt (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term100 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3))))).
Definition term129 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term5 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term84 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term14 (x0 : real) (x1 : real) (x2 : real) := exists y0 : real, ((real_lt x0 x2) /\ (real_le x1 y0)) /\ (~ (real_lt (real_add x0 x1) (real_add x2 y0))).
Definition term88 := S (Nat.add 0 0).
Definition term113 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term11 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((fun y0 : real => ((real_lt x0 x2) /\ (real_le x1 y0)) -> real_lt (real_add x0 x1) (real_add x2 y0)) x3).
Definition term63 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term144 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y0 y1) /\ (real_le y2 y3)) -> real_lt (real_add y0 y2) (real_add y1 y3))) -> False.
Definition term95 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term0 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ (((real_lt x0 x2) /\ (real_le x1 x3)) -> real_lt (real_add x0 x1) (real_add x2 x3)).
Definition term126 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3))))).
Definition term51 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1).
Definition term74 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := and ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) x3) (real_of_num (NUMERAL 0)))).
Definition term2 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_lt x0 x1) /\ (real_le x2 x3).
Definition term105 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term94 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term117 := real_mul (real_of_num (NUMERAL 0)).
Definition term69 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3))).
Definition term45 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term56 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) x3) (real_of_num (NUMERAL 0))).
Definition term66 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add x0 (real_add x1 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3))).
Definition term97 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3))))) (real_of_num (NUMERAL 0)).
Definition term145 := ((~ (forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y0 y1) /\ (real_le y2 y3)) -> real_lt (real_add y0 y2) (real_add y1 y3))) -> False) -> forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y0 y1) /\ (real_le y2 y3)) -> real_lt (real_add y0 y2) (real_add y1 y3).
Definition term9 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => ((real_lt x0 x2) /\ (real_le x1 y0)) -> real_lt (real_add x0 x1) (real_add x2 y0)) x3.
Definition term42 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term18 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => forall y1 : real, ((real_lt x0 x1) /\ (real_le y0 y1)) -> real_lt (real_add x0 y0) (real_add x1 y1)) x2.
Definition term133 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term35 := fun y0 : real => forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y0 y1) /\ (real_le y2 y3)) -> real_lt (real_add y0 y2) (real_add y1 y3).
Definition term26 (x0 : real) := fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt x0 y0) /\ (real_le y1 y2)) -> real_lt (real_add x0 y1) (real_add y0 y2).
Definition term29 (x0 : real) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt x0 y0) /\ (real_le y1 y2)) -> real_lt (real_add x0 y1) (real_add y0 y2)) x1).
Definition term82 := fun y0 : real => exists y1 : real, exists y2 : real, exists y3 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2) y3) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_add y2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y3)))) (real_of_num (NUMERAL 0))).
Definition term80 (x0 : real) := fun y0 : real => exists y1 : real, exists y2 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) y2) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_add y1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y2)))) (real_of_num (NUMERAL 0))).
Definition term40 := fun y0 : real => exists y1 : real, exists y2 : real, exists y3 : real, ((real_lt y0 y1) /\ (real_le y2 y3)) /\ (~ (real_lt (real_add y0 y2) (real_add y1 y3))).
Definition term31 (x0 : real) := fun y0 : real => exists y1 : real, exists y2 : real, ((real_lt x0 y0) /\ (real_le y1 y2)) /\ (~ (real_lt (real_add x0 y1) (real_add y0 y2))).
Definition term70 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_ge (real_sub (real_add x0 x1) (real_add x2 x3)).
Definition term125 (x0 : real) (x1 : real) := real_add (real_of_num (NUMERAL 0)) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term92 := real_of_num (NUMERAL (BIT1 0)).
Definition term13 (x0 : real) (x1 : real) (x2 : real) := fun y0 : real => ((real_lt x0 x2) /\ (real_le x1 y0)) /\ (~ (real_lt (real_add x0 x1) (real_add x2 y0))).
Definition term77 (x0 : real) (x1 : real) (x2 : real) := exists y0 : real, ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) y0) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)))) (real_of_num (NUMERAL 0))).
Definition term118 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term10 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_lt x0 x2) /\ (real_le x1 x3)) -> real_lt (real_add x0 x1) (real_add x2 x3).
Definition term12 (x0 : real) (x1 : real) (x2 : real) := fun y0 : real => ~ ((fun y1 : real => ((real_lt x0 x2) /\ (real_le x1 y1)) -> real_lt (real_add x0 x1) (real_add x2 y1)) y0).
Definition term27 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt x0 y0) /\ (real_le y1 y2)) -> real_lt (real_add x0 y1) (real_add y0 y2)) x1.
Definition term1 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_lt x0 x2) /\ (real_le x1 x3)) /\ (~ (real_lt (real_add x0 x1) (real_add x2 x3))).
Definition term91 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term76 (x0 : real) (x1 : real) (x2 : real) := fun y0 : real => ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) y0) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)))) (real_of_num (NUMERAL 0))).
Definition term75 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) x3) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))) (real_of_num (NUMERAL 0))).
Definition term71 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))).
Definition term139 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term43 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term115 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term122 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)).
Definition term130 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term108 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3))))) (real_of_num (NUMERAL 0)).
Definition term46 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1).
Definition term120 := real_add (real_of_num (NUMERAL 0)).
Definition term36 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, forall y3 : real, ((real_lt y0 y1) /\ (real_le y2 y3)) -> real_lt (real_add y0 y2) (real_add y1 y3)) x0.
Definition term135 (x0 : real) (x1 : real) := ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term103 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term49 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term3 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_lt (real_add x0 x1) (real_add x2 x3).
Definition term87 := NUMERAL (BIT1 0).
Definition term72 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))) (real_of_num (NUMERAL 0)).
Definition term107 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term102 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term123 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term85 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term134 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term101 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term50 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term141 := real_gt (real_of_num (NUMERAL 0)).
Definition term59 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_sub (real_add x0 x1) (real_add x2 x3).
Definition term67 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)).
