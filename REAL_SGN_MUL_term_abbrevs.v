Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term73 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term39 (x0 : real -> Prop) := ~ (all x0).
Definition term87 (x0 : real) (x1 : real) := or (real_gt (real_sub (real_mul (real_mul x0 x1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul x1 (real_inv (real_abs x1))))) (real_of_num (NUMERAL 0))).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_inv (real_mul x0 y0)) = (real_mul (real_inv x0) (real_inv y0))) x1.
Definition term11 (x0 : real) (x1 : real) := (fun y0 : real => (real_abs (real_mul x0 y0)) = (real_mul (real_abs x0) (real_abs y0))) x1.
Definition term18 (x0 : real) (x1 : real) := real_mul (real_mul x0 x1) (real_inv (real_abs (real_mul x0 x1))).
Definition term70 := real_of_num (NUMERAL 0).
Definition term59 (x0 : real) (x1 : real) := real_mul (real_inv (real_abs x0)) (real_mul x1 (real_inv (real_abs x1))).
Definition term103 (x0 : real) := (fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0.
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term29 (x0 : real) (x1 : real) := real_mul (real_sgn x0) (real_sgn x1).
Definition term57 (x0 : real) (x1 : real) := real_mul x0 (real_mul (real_inv (real_abs x0)) (real_mul x1 (real_inv (real_abs x1)))).
Definition term67 (x0 : real) (x1 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_mul x1 (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1))))).
Definition term4 (x0 : real) (x1 : real) := real_mul (real_inv x0) (real_inv x1).
Definition term41 (x0 : real) := ~ (forall y0 : real, (real_mul (real_mul x0 y0) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs y0)))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul y0 (real_inv (real_abs y0))))).
Definition term77 := real_neg (real_of_num (NUMERAL 0)).
Definition term44 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_mul (real_mul x0 y0) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs y0)))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul y0 (real_inv (real_abs y0))))) x1).
Definition term60 (x0 : real) (x1 : real) := real_mul x1 (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1))).
Definition term7 (x0 : real) (x1 : real) := (fun y0 : real => (real_div x0 y0) = (real_mul x0 (real_inv y0))) x1.
Definition term95 (x0 : Prop) := exists y0 : real, x0.
Definition term110 := exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term79 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term38 := forall y0 : real, forall y1 : real, (real_mul (real_mul y0 y1) (real_mul (real_inv (real_abs y0)) (real_inv (real_abs y1)))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul y1 (real_inv (real_abs y1)))).
Definition term37 := forall y0 : real, forall y1 : real, (real_sgn (real_mul y0 y1)) = (real_mul (real_sgn y0) (real_sgn y1)).
Definition term93 := exists y0 : real, exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term55 := exists y0 : real, exists y1 : real, ~ ((real_mul (real_mul y0 y1) (real_mul (real_inv (real_abs y0)) (real_inv (real_abs y1)))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul y1 (real_inv (real_abs y1))))).
Definition term112 := or (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term62 (x0 : real) (x1 : real) := real_sub (real_mul (real_mul x0 x1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)))).
Definition term27 (x0 : real) := real_mul (real_sgn x0).
Definition term66 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_mul x1 (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_mul x1 (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)))))).
Definition term58 (x0 : real) := real_inv (real_abs x0).
Definition term50 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_mul (real_mul y1 y2) (real_mul (real_inv (real_abs y1)) (real_inv (real_abs y2)))) = (real_mul (real_mul y1 (real_inv (real_abs y1))) (real_mul y2 (real_inv (real_abs y2))))) y0).
Definition term42 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_mul (real_mul x0 y1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs y1)))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul y1 (real_inv (real_abs y1))))) y0).
Definition term85 (x0 : real) (x1 : real) := real_gt (real_sub (real_mul (real_mul x0 x1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul x1 (real_inv (real_abs x1))))).
Definition term53 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_mul (real_mul y1 y2) (real_mul (real_inv (real_abs y1)) (real_inv (real_abs y2)))) = (real_mul (real_mul y1 (real_inv (real_abs y1))) (real_mul y2 (real_inv (real_abs y2))))) y0).
Definition term36 := fun y0 : real => forall y1 : real, (real_mul (real_mul y0 y1) (real_mul (real_inv (real_abs y0)) (real_inv (real_abs y1)))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul y1 (real_inv (real_abs y1)))).
Definition term35 := fun y0 : real => forall y1 : real, (real_sgn (real_mul y0 y1)) = (real_mul (real_sgn y0) (real_sgn y1)).
Definition term61 (x0 : real) (x1 : real) := real_mul x0 (real_mul x1 (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)))).
Definition term69 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term32 (x0 : real) := fun y0 : real => (real_mul (real_mul x0 y0) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs y0)))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul y0 (real_inv (real_abs y0)))).
Definition term89 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term20 (x0 : real) (x1 : real) := real_inv (real_mul (real_abs x0) (real_abs x1)).
Definition term28 (x0 : real) := real_mul (real_mul x0 (real_inv (real_abs x0))).
Definition term56 (x0 : real) (x1 : real) := (real_gt (real_sub (real_mul (real_mul x0 x1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul x1 (real_inv (real_abs x1))))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_mul (real_mul x0 x1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul x1 (real_inv (real_abs x1)))))) (real_of_num (NUMERAL 0))).
Definition term98 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term114 := (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term23 (x0 : real) (x1 : real) := real_mul (real_mul x0 x1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1))).
Definition term49 := ~ (forall y0 : real, forall y1 : real, (real_mul (real_mul y0 y1) (real_mul (real_inv (real_abs y0)) (real_inv (real_abs y1)))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul y1 (real_inv (real_abs y1))))).
Definition term116 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term78 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term76 (x0 : real) (x1 : real) := real_neg (real_sub (real_mul (real_mul x0 x1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul x1 (real_inv (real_abs x1))))).
Definition term34 (x0 : real) := forall y0 : real, (real_mul (real_mul x0 y0) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs y0)))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul y0 (real_inv (real_abs y0)))).
Definition term99 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term84 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term102 := fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term12 (x0 : real) (x1 : real) := real_abs (real_mul x0 x1).
Definition term52 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_mul (real_mul y0 y1) (real_mul (real_inv (real_abs y0)) (real_inv (real_abs y1)))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul y1 (real_inv (real_abs y1))))) x0).
Definition term92 := fun y0 : real => exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term65 (x0 : real) (x1 : real) := real_sub (real_mul x0 (real_mul x1 (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1))))) (real_mul x0 (real_mul x1 (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1))))).
Definition term108 := @eq Prop (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term107 := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0)).
Definition term40 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term75 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1))))).
Definition term51 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_mul y0 y1) (real_mul (real_inv (real_abs y0)) (real_inv (real_abs y1)))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul y1 (real_inv (real_abs y1))))) x0.
Definition term9 (x0 : real) := (fun y0 : real => forall y1 : real, (real_abs (real_mul y0 y1)) = (real_mul (real_abs y0) (real_abs y1))) x0.
Definition term5 (x0 : real) := (fun y0 : real => forall y1 : real, (real_div y0 y1) = (real_mul y0 (real_inv y1))) x0.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_inv (real_mul y0 y1)) = (real_mul (real_inv y0) (real_inv y1))) x0.
Definition term115 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term68 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term117 := (~ (forall y0 : real, forall y1 : real, (real_mul (real_mul y0 y1) (real_mul (real_inv (real_abs y0)) (real_inv (real_abs y1)))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul y1 (real_inv (real_abs y1)))))) -> False.
Definition term19 (x0 : real) (x1 : real) := real_inv (real_abs (real_mul x0 x1)).
Definition term48 (x0 : real) := exists y0 : real, ~ ((real_mul (real_mul x0 y0) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs y0)))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul y0 (real_inv (real_abs y0))))).
Definition term63 (x0 : real) (x1 : real) := real_sub (real_mul x0 (real_mul x1 (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1))))).
Definition term24 (x0 : real) (x1 : real) := @eq real (real_sgn (real_mul x0 x1)).
Definition term14 (x0 : real) := (fun y0 : real => (real_sgn y0) = (real_div y0 (real_abs y0))) x0.
Definition term43 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul (real_mul x0 y0) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs y0)))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul y0 (real_inv (real_abs y0))))) x1.
Definition term6 (x0 : real) := forall y0 : real, (real_div x0 y0) = (real_mul x0 (real_inv y0)).
Definition term31 (x0 : real) := fun y0 : real => (real_sgn (real_mul x0 y0)) = (real_mul (real_sgn x0) (real_sgn y0)).
Definition term74 := real_mul (real_of_num (NUMERAL 0)).
Definition term94 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term54 := fun y0 : real => exists y1 : real, ~ ((real_mul (real_mul y0 y1) (real_mul (real_inv (real_abs y0)) (real_inv (real_abs y1)))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul y1 (real_inv (real_abs y1))))).
Definition term106 := fun y0 : real => ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term3 (x0 : real) (x1 : real) := real_inv (real_mul x0 x1).
Definition term100 := exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term90 := fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term118 := ((~ (forall y0 : real, forall y1 : real, (real_mul (real_mul y0 y1) (real_mul (real_inv (real_abs y0)) (real_inv (real_abs y1)))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul y1 (real_inv (real_abs y1)))))) -> False) -> forall y0 : real, forall y1 : real, (real_mul (real_mul y0 y1) (real_mul (real_inv (real_abs y0)) (real_inv (real_abs y1)))) = (real_mul (real_mul y0 (real_inv (real_abs y0))) (real_mul y1 (real_inv (real_abs y1)))).
Definition term64 (x0 : real) (x1 : real) := real_sub (real_mul (real_mul x0 x1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul x1 (real_inv (real_abs x1)))).
Definition term16 (x0 : real) (x1 : real) := real_sgn (real_mul x0 x1).
Definition term30 (x0 : real) (x1 : real) := real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul x1 (real_inv (real_abs x1))).
Definition term105 (x0 : real) := ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term47 (x0 : real) := fun y0 : real => ~ ((real_mul (real_mul x0 y0) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs y0)))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul y0 (real_inv (real_abs y0))))).
Definition term33 (x0 : real) := forall y0 : real, (real_sgn (real_mul x0 y0)) = (real_mul (real_sgn x0) (real_sgn y0)).
Definition term10 (x0 : real) := forall y0 : real, (real_abs (real_mul x0 y0)) = (real_mul (real_abs x0) (real_abs y0)).
Definition term1 (x0 : real) := forall y0 : real, (real_inv (real_mul x0 y0)) = (real_mul (real_inv x0) (real_inv y0)).
Definition term25 (x0 : real) (x1 : real) := @eq real (real_mul (real_mul x0 x1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)))).
Definition term45 (x0 : real) (x1 : real) := ~ ((real_mul (real_mul x0 x1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul x1 (real_inv (real_abs x1))))).
Definition term109 := fun y0 : real => (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term83 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_mul (real_mul x0 x1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul x1 (real_inv (real_abs x1)))))) (real_of_num (NUMERAL 0)).
Definition term86 (x0 : real) (x1 : real) := real_gt (real_sub (real_mul (real_mul x0 x1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul x1 (real_inv (real_abs x1))))) (real_of_num (NUMERAL 0)).
Definition term13 (x0 : real) (x1 : real) := real_mul (real_abs x0) (real_abs x1).
Definition term46 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_mul (real_mul x0 y1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs y1)))) = (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul y1 (real_inv (real_abs y1))))) y0).
Definition term26 (x0 : real) := real_mul x0 (real_inv (real_abs x0)).
Definition term88 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term104 (x0 : real) := or ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term81 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_mul (real_mul x0 x1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul x1 (real_inv (real_abs x1)))))).
Definition term8 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
Definition term17 (x0 : real) (x1 : real) := real_div (real_mul x0 x1) (real_abs (real_mul x0 x1)).
Definition term21 (x0 : real) (x1 : real) := real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)).
Definition term71 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term22 (x0 : real) (x1 : real) := real_mul (real_mul x0 x1).
Definition term113 := or (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term80 (x0 : real) (x1 : real) := @eq real (real_neg (real_sub (real_mul (real_mul x0 x1) (real_mul (real_inv (real_abs x0)) (real_inv (real_abs x1)))) (real_mul (real_mul x0 (real_inv (real_abs x0))) (real_mul x1 (real_inv (real_abs x1)))))).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term72 := NUMERAL (BIT1 0).
Definition term101 := (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term91 := exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term15 (x0 : real) := real_div x0 (real_abs x0).
Definition term111 := exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term82 := real_gt (real_of_num (NUMERAL 0)).