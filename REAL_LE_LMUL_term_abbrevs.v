Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term112 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term5 (x0 : real) (x1 : real) := forall y0 : real, (real_sub (real_mul x0 x1) (real_mul x0 y0)) = (real_mul x0 (real_sub x1 y0)).
Definition term50 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term137 (x0 : real) (x1 : real) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) (real_sub x0 (real_of_num (NUMERAL 0)))) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub y0 x1))) -> real_le (real_of_num (NUMERAL 0)) (real_sub (real_mul x0 y0) (real_mul x0 x1)).
Definition term32 := real_of_num (NUMERAL 0).
Definition term84 (x0 : real) (x1 : real) := or ((real_le x1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1)))).
Definition term129 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_of_num (NUMERAL 0)) (real_sub x0 (real_of_num (NUMERAL 0)))) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub x1 x2)).
Definition term91 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term72 (x0 : real) (x1 : real) := real_sub (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term152 (x0 : real) (x1 : real) (x2 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub x1 x2))) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_sub x1 x2)).
Definition term155 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term94 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term107 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1).
Definition term153 := fun y0 : real => True.
Definition term41 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term122 (x0 : real) (x1 : real) := (~ ((real_le x1 x0) = (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1)))) -> False.
Definition term106 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term118 (x0 : real) (x1 : real) := real_gt (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term23 (x0 : real) (x1 : real) := ~ ((real_le x1 x0) = (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1))).
Definition term69 (x0 : real) (x1 : real) := real_ge (real_sub (real_sub x0 x1) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term61 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term33 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term40 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term34 (x0 : real) (x1 : real) := ~ (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1)).
Definition term154 := forall y0 : real, True.
Definition term78 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term156 (x0 : Prop) := forall y0 : real, x0.
Definition term28 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term125 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term132 (x0 : real) (x1 : real) (x2 : real) := real_le (real_mul x1 x0) (real_mul x1 x2).
Definition term73 (x0 : real) (x1 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term100 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term56 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term89 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term75 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term147 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) (real_sub y0 (real_of_num (NUMERAL 0)))) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub y2 y1))) -> real_le (real_of_num (NUMERAL 0)) (real_sub (real_mul y0 y2) (real_mul y0 y1)).
Definition term146 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2).
Definition term143 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) (real_sub x0 (real_of_num (NUMERAL 0)))) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub y1 y0))) -> real_le (real_of_num (NUMERAL 0)) (real_sub (real_mul x0 y1) (real_mul x0 y0)).
Definition term142 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le y0 y1)) -> real_le (real_mul x0 y0) (real_mul x0 y1).
Definition term13 := forall y0 : real, forall y1 : real, forall y2 : real, (real_sub (real_mul y0 y1) (real_mul y0 y2)) = (real_mul y0 (real_sub y1 y2)).
Definition term12 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_sub y1 y2)) = (real_sub (real_mul y0 y1) (real_mul y0 y2)).
Definition term9 (x0 : real) := forall y0 : real, forall y1 : real, (real_sub (real_mul x0 y0) (real_mul x0 y1)) = (real_mul x0 (real_sub y0 y1)).
Definition term8 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul x0 (real_sub y0 y1)) = (real_sub (real_mul x0 y0) (real_mul x0 y1)).
Definition term43 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term47 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term19 (x0 : real) := real_sub x0 (real_of_num (NUMERAL 0)).
Definition term101 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term37 (x0 : real) (x1 : real) := real_sub (real_of_num (NUMERAL 0)) (real_sub x0 x1).
Definition term148 := real_le (real_of_num (NUMERAL 0)).
Definition term138 (x0 : real) (x1 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 y0)) -> real_le (real_mul x1 x0) (real_mul x1 y0).
Definition term15 (x0 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 y0).
Definition term131 (x0 : real) (x1 : real) (x2 : real) := imp ((real_le (real_of_num (NUMERAL 0)) (real_sub x0 (real_of_num (NUMERAL 0)))) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub x1 x2))).
Definition term60 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term2 (x0 : real) (x1 : real) := fun y0 : real => (real_mul x1 (real_sub x0 y0)) = (real_sub (real_mul x1 x0) (real_mul x1 y0)).
Definition term4 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x1 (real_sub x0 y0)) = (real_sub (real_mul x1 x0) (real_mul x1 y0)).
Definition term31 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term79 (x0 : real) (x1 : real) := real_ge (real_sub (real_sub x0 x1) (real_of_num (NUMERAL 0))).
Definition term126 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term25 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1).
Definition term136 (x0 : real) (x1 : real) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 y0)) -> real_le (real_mul x1 x0) (real_mul x1 y0).
Definition term59 (x0 : real) (x1 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_sub x0 x1)).
Definition term141 (x0 : real) := fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) (real_sub x0 (real_of_num (NUMERAL 0)))) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub y1 y0))) -> real_le (real_of_num (NUMERAL 0)) (real_sub (real_mul x0 y1) (real_mul x0 y0)).
Definition term140 (x0 : real) := fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le y0 y1)) -> real_le (real_mul x0 y0) (real_mul x0 y1).
Definition term7 (x0 : real) := fun y0 : real => forall y1 : real, (real_sub (real_mul x0 y0) (real_mul x0 y1)) = (real_mul x0 (real_sub y0 y1)).
Definition term6 (x0 : real) := fun y0 : real => forall y1 : real, (real_mul x0 (real_sub y0 y1)) = (real_sub (real_mul x0 y0) (real_mul x0 y1)).
Definition term65 (x0 : real) (x1 : real) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term110 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term51 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term16 (x0 : real) (x1 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 y0)) x1.
Definition term121 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term76 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term36 := real_sub (real_of_num (NUMERAL 0)).
Definition term22 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_sub (real_mul x0 x1) (real_mul x0 y0)) = (real_mul x0 (real_sub x1 y0))) x2.
Definition term120 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term128 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x1 x2).
Definition term55 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term115 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term81 (x0 : real) (x1 : real) := and (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term116 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term53 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term92 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term105 (x0 : real) (x1 : real) := real_gt (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term97 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term35 (x0 : real) (x1 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_sub x0 x1)) (real_of_num (NUMERAL 0)).
Definition term86 (x0 : real) (x1 : real) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))).
Definition term24 (x0 : real) (x1 : real) := ((real_le x1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1)))) \/ ((~ (real_le x1 x0)) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1))).
Definition term14 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y0 y1)) x0.
Definition term87 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term90 := S (Nat.add 0 0).
Definition term109 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term124 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term42 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term3 (x0 : real) (x1 : real) := fun y0 : real => (real_sub (real_mul x0 x1) (real_mul x0 y0)) = (real_mul x0 (real_sub x1 y0)).
Definition term96 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term71 (x0 : real) (x1 : real) := real_sub (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term63 (x0 : real) (x1 : real) := and (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term30 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1).
Definition term133 (x0 : real) (x1 : real) (x2 : real) := real_le (real_of_num (NUMERAL 0)) (real_sub (real_mul x1 x0) (real_mul x1 x2)).
Definition term95 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term113 := real_mul (real_of_num (NUMERAL 0)).
Definition term21 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_sub (real_mul x0 y0) (real_mul x0 y1)) = (real_mul x0 (real_sub y0 y1))) x1.
Definition term29 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term123 (x0 : real) (x1 : real) := ((~ ((real_le x1 x0) = (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1)))) -> False) -> (real_le x1 x0) = (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1)).
Definition term127 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) (real_sub x0 (real_of_num (NUMERAL 0)))).
Definition term54 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term67 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term39 (x0 : real) (x1 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term38 (x0 : real) (x1 : real) := real_sub (real_of_num (NUMERAL 0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term130 (x0 : real) (x1 : real) (x2 : real) := imp ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x1 x2)).
Definition term150 (x0 : real) (x1 : real) (x2 : real) := imp ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub x1 x2))).
Definition term102 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term45 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term145 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) (real_sub y0 (real_of_num (NUMERAL 0)))) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub y2 y1))) -> real_le (real_of_num (NUMERAL 0)) (real_sub (real_mul y0 y2) (real_mul y0 y1)).
Definition term144 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y1 y2)) -> real_le (real_mul y0 y1) (real_mul y0 y2).
Definition term11 := fun y0 : real => forall y1 : real, forall y2 : real, (real_sub (real_mul y0 y1) (real_mul y0 y2)) = (real_mul y0 (real_sub y1 y2)).
Definition term10 := fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_sub y1 y2)) = (real_sub (real_mul y0 y1) (real_mul y0 y2)).
Definition term134 (x0 : real) (x1 : real) (x2 : real) := ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x0 x2)) -> real_le (real_mul x1 x0) (real_mul x1 x2).
Definition term58 (x0 : real) (x1 : real) := real_add (real_of_num (NUMERAL 0)) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term66 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term48 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term135 (x0 : real) (x1 : real) (x2 : real) := ((real_le (real_of_num (NUMERAL 0)) (real_sub x1 (real_of_num (NUMERAL 0)))) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x2))) -> real_le (real_of_num (NUMERAL 0)) (real_sub (real_mul x1 x0) (real_mul x1 x2)).
Definition term52 := real_of_num (NUMERAL (BIT1 0)).
Definition term0 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_sub x1 x2).
Definition term114 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term62 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term85 (x0 : real) (x1 : real) := or ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))).
Definition term44 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term1 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_mul x1 x0) (real_mul x1 x2).
Definition term17 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term93 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term46 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term74 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term117 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term139 (x0 : real) (x1 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) (real_sub x0 (real_of_num (NUMERAL 0)))) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub y0 x1))) -> real_le (real_of_num (NUMERAL 0)) (real_sub (real_mul x0 y0) (real_mul x0 x1)).
Definition term149 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub x1 x2)).
Definition term70 (x0 : real) (x1 : real) := real_sub (real_sub x0 x1).
Definition term151 (x0 : real) (x1 : real) (x2 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_sub x1 x2)).
Definition term80 (x0 : real) (x1 : real) := and (~ (real_le x0 x1)).
Definition term27 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term18 (x0 : real) := (fun y0 : real => (real_sub y0 (real_of_num (NUMERAL 0))) = y0) x0.
Definition term111 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term99 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term64 (x0 : real) (x1 : real) := (real_le x1 x0) /\ (~ (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1))).
Definition term68 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1).
Definition term57 := real_add (real_of_num (NUMERAL 0)).
Definition term20 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_sub (real_mul y0 y1) (real_mul y0 y2)) = (real_mul y0 (real_sub y1 y2))) x0.
Definition term104 (x0 : real) (x1 : real) := ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term77 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term82 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) /\ (real_le (real_of_num (NUMERAL 0)) (real_sub x0 x1)).
Definition term49 := NUMERAL (BIT1 0).
Definition term103 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term98 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term108 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term88 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term83 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term26 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term119 := real_gt (real_of_num (NUMERAL 0)).