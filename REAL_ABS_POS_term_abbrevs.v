Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term56 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term0 (x0 : real -> Prop) := ~ (all x0).
Definition term49 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term39 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term44 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term13 := real_of_num (NUMERAL 0).
Definition term5 (x0 : real) := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_abs y0)) x0.
Definition term6 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_abs x0).
Definition term2 := ~ (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0)).
Definition term8 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) (real_abs x0)).
Definition term34 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term64 := ((~ (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0))) -> False) -> forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0).
Definition term18 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)).
Definition term45 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term3 := exists y0 : real, ~ ((fun y1 : real => real_le (real_of_num (NUMERAL 0)) (real_abs y1)) y0).
Definition term54 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term23 (x0 : real) (x1 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x1).
Definition term62 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term19 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) (real_of_num (NUMERAL 0)).
Definition term21 := exists y0 : real, real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_of_num (NUMERAL 0)).
Definition term28 (x0 : real) := real_gt x0 (real_of_num (NUMERAL 0)).
Definition term61 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term25 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term51 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term46 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term10 := fun y0 : real => ~ (real_le (real_of_num (NUMERAL 0)) (real_abs y0)).
Definition term1 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term32 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term36 := S (Nat.add 0 0).
Definition term52 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term53 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term63 := (~ (forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0))) -> False.
Definition term29 (x0 : real) := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term57 := real_mul (real_of_num (NUMERAL 0)).
Definition term22 (x0 : real) (x1 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) x1.
Definition term47 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term26 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term43 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term16 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0).
Definition term24 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0))).
Definition term11 := exists y0 : real, ~ (real_le (real_of_num (NUMERAL 0)) (real_abs y0)).
Definition term15 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)).
Definition term40 := real_of_num (NUMERAL (BIT1 0)).
Definition term58 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term12 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_abs x0)) (real_of_num (NUMERAL 0)).
Definition term4 := fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_abs y0).
Definition term59 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term50 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term7 (x0 : real) := ~ ((fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_abs y0)) x0).
Definition term9 := fun y0 : real => ~ ((fun y1 : real => real_le (real_of_num (NUMERAL 0)) (real_abs y1)) y0).
Definition term17 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) (real_abs x0)).
Definition term20 := fun y0 : real => real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs y0)) (real_of_num (NUMERAL 0)).
Definition term14 (x0 : real) := real_sub (real_of_num (NUMERAL 0)) (real_abs x0).
Definition term30 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term31 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term27 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term55 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term41 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term42 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term65 := forall y0 : real, real_le (real_of_num (NUMERAL 0)) (real_abs y0).
Definition term37 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term35 := NUMERAL (BIT1 0).
Definition term48 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term38 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term33 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term60 := real_gt (real_of_num (NUMERAL 0)).
