Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term186 (x0 : real) := real_gt (real_neg (real_sub (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x0)).
Definition term136 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term10 (x0 : real) := @eq real (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term175 (x0 : real) (x1 : real) (x2 : real) := or (real_gt (real_sub (real_mul x0 (real_mul x1 x2)) (real_mul (real_mul x0 x1) x2)) (real_of_num (NUMERAL 0))).
Definition term155 (x0 : real) (x1 : real) := or (real_gt (real_sub (real_mul x1 x0) (real_mul x0 x1)) (real_of_num (NUMERAL 0))).
Definition term100 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term20 (x0 : real -> Prop) := ~ (all x0).
Definition term119 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term1 (a0 : Type') (x0 : type1400 a0) := (forall y0 : a0, forall y1 : a0, (x0 y0 y1) = (x0 y1 y0)) /\ ((forall y0 : a0, forall y1 : a0, forall y2 : a0, (x0 y0 (x0 y1 y2)) = (x0 (x0 y0 y1) y2)) /\ (forall y0 : a0, (x0 (@neutral a0 x0) y0) = y0)).
Definition term184 (x0 : real) := real_neg (real_sub (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x0).
Definition term44 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul x1 x2).
Definition term108 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term125 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term180 (x0 : real) := real_sub (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x0.
Definition term126 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term154 (x0 : real) (x1 : real) := real_gt (real_sub (real_mul x1 x0) (real_mul x0 x1)) (real_of_num (NUMERAL 0)).
Definition term99 (x0 : nat) := real_neg (real_of_num x0).
Definition term107 := real_of_num (NUMERAL 0).
Definition term49 (x0 : real) (x1 : real) := fun y0 : real => ~ ((real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0)).
Definition term18 := and (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)).
Definition term15 := and (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)).
Definition term204 (x0 : real) := (fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0.
Definition term50 (x0 : real) (x1 : real) := exists y0 : real, ~ ((real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0)).
Definition term30 (x0 : real) := exists y0 : real, ~ ((real_mul x0 y0) = (real_mul y0 x0)).
Definition term114 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term128 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term225 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term198 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term12 := fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0.
Definition term11 := fun y0 : real => (real_mul (@neutral real real_mul) y0) = y0.
Definition term166 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul x0 (real_mul x1 x2)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_mul x1 x2))).
Definition term148 (x0 : real) (x1 : real) := @eq real (real_neg (real_sub (real_mul x1 x0) (real_mul x0 x1))).
Definition term144 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term40 (x0 : real) (x1 : real) := ~ (forall y0 : real, (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0)).
Definition term22 (x0 : real) := ~ (forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0)).
Definition term187 (x0 : real) := real_gt (real_neg (real_sub (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x0)) (real_of_num (NUMERAL 0)).
Definition term102 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term228 := (~ ((forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0)))) -> False.
Definition term194 := (exists y0 : real, exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((exists y0 : real, exists y1 : real, exists y2 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))).
Definition term86 := (exists y0 : real, exists y1 : real, ~ ((real_mul y0 y1) = (real_mul y1 y0))) \/ ((exists y0 : real, exists y1 : real, exists y2 : real, ~ ((real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2))) \/ (exists y0 : real, ~ ((real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0))).
Definition term149 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_mul x1 x0) (real_mul x0 x1))).
Definition term35 (x0 : real) := forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0).
Definition term217 := ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term139 := real_neg (real_of_num (NUMERAL 0)).
Definition term69 := ~ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0).
Definition term25 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1.
Definition term112 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term106 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term94 (x0 : real) (x1 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1).
Definition term26 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1).
Definition term134 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term85 := (~ (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0))) \/ (~ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0))).
Definition term138 (x0 : real) (x1 : real) := real_neg (real_sub (real_mul x1 x0) (real_mul x0 x1)).
Definition term192 := (exists y0 : real, exists y1 : real, exists y2 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term0 (a0 : Type') (x0 : type1400 a0) := (fun y0 : type1400 a0 => (@monoidal a0 y0) = ((forall y1 : a0, forall y2 : a0, (y0 y1 y2) = (y0 y2 y1)) /\ ((forall y1 : a0, forall y2 : a0, forall y3 : a0, (y0 y1 (y0 y2 y3)) = (y0 (y0 y1 y2) y3)) /\ (forall y1 : a0, (y0 (@neutral a0 y0) y1) = y1)))) x0.
Definition term90 (x0 : real) (x1 : real) := real_sub (real_mul x0 x1).
Definition term174 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub (real_mul x0 (real_mul x1 x2)) (real_mul (real_mul x0 x1) x2)) (real_of_num (NUMERAL 0)).
Definition term179 (x0 : real) := real_sub (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term124 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term101 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term163 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_mul x0 (real_mul x1 x2)).
Definition term110 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term196 (x0 : Prop) := exists y0 : real, x0.
Definition term211 := exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term145 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term88 := forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0).
Definition term82 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2).
Definition term64 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term83 := or (~ (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0))).
Definition term77 := or (~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2))).
Definition term177 := exists y0 : real, exists y1 : real, exists y2 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term161 := exists y0 : real, exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term68 := exists y0 : real, exists y1 : real, exists y2 : real, ~ ((real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)).
Definition term59 (x0 : real) := exists y0 : real, exists y1 : real, ~ ((real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1)).
Definition term39 := exists y0 : real, exists y1 : real, ~ ((real_mul y0 y1) = (real_mul y1 y0)).
Definition term185 (x0 : real) := @eq real (real_neg (real_sub (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x0)).
Definition term143 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term213 := or (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term43 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0)) x2.
Definition term113 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term105 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term93 (x0 : real) (x1 : real) := real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)).
Definition term70 := exists y0 : real, ~ ((fun y1 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y1) = y1) y0).
Definition term61 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, (real_mul y1 (real_mul y2 y3)) = (real_mul (real_mul y1 y2) y3)) y0).
Definition term52 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_mul x0 (real_mul y1 y2)) = (real_mul (real_mul x0 y1) y2)) y0).
Definition term41 (x0 : real) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => (real_mul x0 (real_mul x1 y1)) = (real_mul (real_mul x0 x1) y1)) y0).
Definition term32 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_mul y1 y2) = (real_mul y2 y1)) y0).
Definition term23 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_mul x0 y1) = (real_mul y1 x0)) y0).
Definition term220 := real_lt (real_of_num (NUMERAL 0)).
Definition term66 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, (real_mul y1 (real_mul y2 y3)) = (real_mul (real_mul y1 y2) y3)) y0).
Definition term57 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_mul x0 (real_mul y1 y2)) = (real_mul (real_mul x0 y1) y2)) y0).
Definition term37 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_mul y1 y2) = (real_mul y2 y1)) y0).
Definition term164 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_mul x0 (real_mul x1 x2)) (real_mul (real_mul x0 x1) x2).
Definition term71 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) x0.
Definition term19 := (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0)).
Definition term3 := (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ (forall y0 : real, (real_mul (@neutral real real_mul) y0) = y0)).
Definition term2 (x0 : type1627) := (forall y0 : real, forall y1 : real, (x0 y0 y1) = (x0 y1 y0)) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (x0 y0 (x0 y1 y2)) = (x0 (x0 y0 y1) y2)) /\ (forall y0 : real, (x0 (@neutral real x0) y0) = y0)).
Definition term5 := real_mul (@neutral real real_mul).
Definition term131 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term127 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term120 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term157 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term103 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term162 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_sub (real_mul x0 (real_mul x1 x2)) (real_mul (real_mul x0 x1) x2)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_mul x0 (real_mul x1 x2)) (real_mul (real_mul x0 x1) x2))) (real_of_num (NUMERAL 0))).
Definition term89 (x0 : real) (x1 : real) := (real_gt (real_sub (real_mul x1 x0) (real_mul x0 x1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_mul x1 x0) (real_mul x0 x1))) (real_of_num (NUMERAL 0))).
Definition term199 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term215 := (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term60 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)).
Definition term51 (x0 : real) := ~ (forall y0 : real, forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1)).
Definition term31 := ~ (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)).
Definition term227 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term140 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term190 (x0 : real) := or (real_gt (real_sub (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x0) (real_of_num (NUMERAL 0))).
Definition term55 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term74 := fun y0 : real => ~ ((fun y1 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y1) = y1) y0).
Definition term109 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term153 (x0 : real) (x1 : real) := real_gt (real_sub (real_mul x1 x0) (real_mul x0 x1)).
Definition term200 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term172 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_neg (real_sub (real_mul x0 (real_mul x1 x2)) (real_mul (real_mul x0 x1) x2))) (real_of_num (NUMERAL 0)).
Definition term151 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_mul x1 x0) (real_mul x0 x1))) (real_of_num (NUMERAL 0)).
Definition term152 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term222 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term203 := fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term8 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term65 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) x0).
Definition term36 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0).
Definition term121 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term160 := fun y0 : real => exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term14 := forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0.
Definition term13 := forall y0 : real, (real_mul (@neutral real real_mul) y0) = y0.
Definition term76 := exists y0 : real, ~ ((real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0).
Definition term209 := @eq Prop (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term208 := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0)).
Definition term53 (x0 : real) := fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term33 := fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0).
Definition term21 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term171 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_neg (real_sub (real_mul x0 (real_mul x1 x2)) (real_mul (real_mul x0 x1) x2))).
Definition term46 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0)) x2).
Definition term189 (x0 : real) := real_gt (real_sub (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term34 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0.
Definition term117 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term224 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term178 (x0 : real) := (real_gt (real_sub (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x0)) (real_of_num (NUMERAL 0))).
Definition term173 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub (real_mul x0 (real_mul x1 x2)) (real_mul (real_mul x0 x1) x2)).
Definition term111 := S (Nat.add 0 0).
Definition term141 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term182 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term87 := ~ ((forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0))).
Definition term95 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term123 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term169 (x0 : real) (x1 : real) (x2 : real) := real_neg (real_sub (real_mul x0 (real_mul x1 x2)) (real_mul (real_mul x0 x1) x2)).
Definition term170 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_neg (real_sub (real_mul x0 (real_mul x1 x2)) (real_mul (real_mul x0 x1) x2))).
Definition term129 := real_mul (real_of_num (NUMERAL 0)).
Definition term81 := ~ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0)).
Definition term219 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term54 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1)) x1.
Definition term195 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term92 (x0 : real) (x1 : real) := real_sub (real_mul x0 x1) (real_mul x0 x1).
Definition term115 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term58 (x0 : real) := fun y0 : real => exists y1 : real, ~ ((real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1)).
Definition term38 := fun y0 : real => exists y1 : real, ~ ((real_mul y0 y1) = (real_mul y1 y0)).
Definition term6 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term207 := fun y0 : real => ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term133 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term97 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term216 := or ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term201 := exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term158 := fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term165 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_mul x0 (real_mul x1 x2)) (real_mul x0 (real_mul x1 x2)).
Definition term122 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term75 := fun y0 : real => ~ ((real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0).
Definition term24 (x0 : real) := fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0).
Definition term206 (x0 : real) := ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term62 := fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2).
Definition term56 (x0 : real) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1)) x1).
Definition term176 := fun y0 : real => exists y1 : real, exists y2 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term67 := fun y0 : real => exists y1 : real, exists y2 : real, ~ ((real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)).
Definition term17 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0).
Definition term16 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ (forall y0 : real, (real_mul (@neutral real real_mul) y0) = y0).
Definition term146 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term118 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term168 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_of_num (NUMERAL 0)) (real_mul x0 (real_mul x1 x2)).
Definition term135 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term91 (x0 : real) (x1 : real) := real_sub (real_mul x1 x0) (real_mul x0 x1).
Definition term132 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term4 := real_of_num (NUMERAL (BIT1 0)).
Definition term229 := ((~ ((forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0)))) -> False) -> (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0)).
Definition term218 := ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ (((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))).
Definition term45 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_mul x0 x1) x2.
Definition term72 (x0 : real) := ~ ((fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) x0).
Definition term73 (x0 : real) := ~ ((real_mul (real_of_num (NUMERAL (BIT1 0))) x0) = x0).
Definition term210 := fun y0 : real => (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term80 := (exists y0 : real, exists y1 : real, exists y2 : real, ~ ((real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2))) \/ (exists y0 : real, ~ ((real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0)).
Definition term183 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term79 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2))) \/ (~ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0)).
Definition term29 (x0 : real) := fun y0 : real => ~ ((real_mul x0 y0) = (real_mul y0 x0)).
Definition term48 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (real_mul x0 (real_mul x1 y1)) = (real_mul (real_mul x0 x1) y1)) y0).
Definition term28 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_mul x0 y1) = (real_mul y1 x0)) y0).
Definition term223 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term42 (x0 : real) (x1 : real) := fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term156 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term137 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term116 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term205 (x0 : real) := or ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term47 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_mul x0 (real_mul x1 x2)) = (real_mul (real_mul x0 x1) x2)).
Definition term9 (x0 : real) := @eq real (real_mul (@neutral real real_mul) x0).
Definition term188 (x0 : real) := real_gt (real_sub (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x0).
Definition term27 (x0 : real) (x1 : real) := ~ ((real_mul x1 x0) = (real_mul x0 x1)).
Definition term7 (x0 : real) := real_mul (@neutral real real_mul) x0.
Definition term221 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term104 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term96 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term167 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_mul x1 x2)).
Definition term142 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term147 := real_div (real_of_num (NUMERAL 0)).
Definition term214 := or (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term63 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) x0.
Definition term193 := or (exists y0 : real, exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term191 := or (exists y0 : real, exists y1 : real, exists y2 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term84 := or (exists y0 : real, exists y1 : real, ~ ((real_mul y0 y1) = (real_mul y1 y0))).
Definition term78 := or (exists y0 : real, exists y1 : real, exists y2 : real, ~ ((real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2))).
Definition term197 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term130 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term98 := NUMERAL (BIT1 0).
Definition term202 := (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term159 := exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term181 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term212 := exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term226 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term150 := real_gt (real_of_num (NUMERAL 0)).