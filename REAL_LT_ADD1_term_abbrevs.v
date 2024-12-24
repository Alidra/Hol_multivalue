Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term86 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term3 (x0 : real -> Prop) := ~ (all x0).
Definition term45 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term50 (x0 : real) (x1 : real) := real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term80 (x0 : real) (x1 : real) := real_add (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term29 := real_of_num (NUMERAL 0).
Definition term65 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term36 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term13 (x0 : real) := exists y0 : real, (real_le x0 y0) /\ (~ (real_lt x0 (real_add y0 (real_of_num (NUMERAL (BIT1 0)))))).
Definition term96 (x0 : real) (x1 : real) := real_ge (real_add (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term68 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term5 (x0 : real) := ~ (forall y0 : real, (real_le x0 y0) -> real_lt x0 (real_add y0 (real_of_num (NUMERAL (BIT1 0))))).
Definition term18 (x0 : real) := forall y0 : real, (real_le x0 y0) -> real_lt x0 (real_add y0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term35 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term10 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_le x0 y0) -> real_lt x0 (real_add y0 (real_of_num (NUMERAL (BIT1 0))))) x1).
Definition term57 (x0 : real) := fun y0 : real => (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term30 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term76 (x0 : real) (x1 : real) := (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term25 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term43 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term102 := and ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term52 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term81 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x1).
Definition term63 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term105 := forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term94 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term92 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term60 := exists y0 : real, exists y1 : real, (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term22 := exists y0 : real, exists y1 : real, (real_le y0 y1) /\ (~ (real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0)))))).
Definition term33 (x0 : real) := real_add x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term9 (x0 : real) (x1 : real) := (real_le x0 x1) -> real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term100 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term15 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_le y1 y2) -> real_lt y1 (real_add y2 (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term6 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_le x0 y1) -> real_lt x0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term37 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term99 (x0 : nat) (x1 : nat) := real_ge (real_neg (real_of_num x0)) (real_of_num x1).
Definition term28 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term20 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_le y1 y2) -> real_lt y1 (real_add y2 (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term21 := fun y0 : real => exists y1 : real, (real_le y0 y1) /\ (~ (real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0)))))).
Definition term16 := fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term84 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term46 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term14 := ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term1 (x0 : real) (x1 : real) := (real_le x0 x1) /\ (~ (real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0)))))).
Definition term12 (x0 : real) := fun y0 : real => (real_le x0 y0) /\ (~ (real_lt x0 (real_add y0 (real_of_num (NUMERAL (BIT1 0)))))).
Definition term71 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term89 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term51 (x0 : real) (x1 : real) := real_ge (real_sub x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term73 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term19 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) x0).
Definition term40 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term59 := fun y0 : real => exists y1 : real, (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add y0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term93 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term77 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term66 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term101 := ((NUMERAL (BIT1 0)) = (NUMERAL 0)) /\ ((NUMERAL 0) = (NUMERAL 0)).
Definition term79 (x0 : real) (x1 : real) := real_ge (real_add (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term75 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))).
Definition term32 (x0 : real) (x1 : real) := real_ge (real_sub x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term4 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term17 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term97 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term61 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term64 := S (Nat.add 0 0).
Definition term83 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term38 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term103 := (~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0)))))) -> False.
Definition term42 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term70 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term55 (x0 : real) (x1 : real) := and (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term27 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1).
Definition term74 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term69 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term87 := real_mul (real_of_num (NUMERAL 0)).
Definition term7 (x0 : real) := fun y0 : real => (real_le x0 y0) -> real_lt x0 (real_add y0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term26 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term91 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term72 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term104 := ((~ (forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0)))))) -> False) -> forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_lt y0 (real_add y1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term41 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term34 (x0 : real) (x1 : real) := real_sub x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term47 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term39 := real_of_num (NUMERAL (BIT1 0)).
Definition term48 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term95 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term58 (x0 : real) := exists y0 : real, (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term88 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term2 (x0 : real) (x1 : real) := real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0)))).
Definition term31 (x0 : real) (x1 : real) := ~ (real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term54 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term11 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_le x0 y1) -> real_lt x0 (real_add y1 (real_of_num (NUMERAL (BIT1 0))))) y0).
Definition term78 (x0 : real) (x1 : real) := ((real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term67 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term53 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term49 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term24 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term85 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term98 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term8 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) -> real_lt x0 (real_add y0 (real_of_num (NUMERAL (BIT1 0))))) x1.
Definition term90 := real_add (real_of_num (NUMERAL 0)).
Definition term44 := NUMERAL (BIT1 0).
Definition term82 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term62 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term0 (x0 : real) (x1 : real) := ~ ((real_le x0 x1) -> real_lt x0 (real_add x1 (real_of_num (NUMERAL (BIT1 0))))).
Definition term56 (x0 : real) (x1 : real) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term23 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0)).
