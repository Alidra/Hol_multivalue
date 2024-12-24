Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term197 (x0 : real) := real_gt (real_neg (real_sub (real_add (real_of_num (NUMERAL 0)) x0) x0)).
Definition term143 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term189 (x0 : real) (x1 : real) (x2 : real) := or (real_gt (real_sub (real_add x0 (real_add x1 x2)) (real_add (real_add x0 x1) x2)) (real_of_num (NUMERAL 0))).
Definition term164 (x0 : real) (x1 : real) := or (real_gt (real_sub (real_add x1 x0) (real_add x0 x1)) (real_of_num (NUMERAL 0))).
Definition term108 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term20 (x0 : real -> Prop) := ~ (all x0).
Definition term126 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term1 (a0 : Type') (x0 : type1400 a0) := (forall y0 : a0, forall y1 : a0, (x0 y0 y1) = (x0 y1 y0)) /\ ((forall y0 : a0, forall y1 : a0, forall y2 : a0, (x0 y0 (x0 y1 y2)) = (x0 (x0 y0 y1) y2)) /\ (forall y0 : a0, (x0 (@neutral a0 x0) y0) = y0)).
Definition term195 (x0 : real) := real_neg (real_sub (real_add (real_of_num (NUMERAL 0)) x0) x0).
Definition term115 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term132 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term133 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term163 (x0 : real) (x1 : real) := real_gt (real_sub (real_add x1 x0) (real_add x0 x1)) (real_of_num (NUMERAL 0)).
Definition term107 (x0 : nat) := real_neg (real_of_num x0).
Definition term4 := real_of_num (NUMERAL 0).
Definition term94 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1).
Definition term49 (x0 : real) (x1 : real) := fun y0 : real => ~ ((real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0)).
Definition term18 := and (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)).
Definition term15 := and (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)).
Definition term215 (x0 : real) := (fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0.
Definition term50 (x0 : real) (x1 : real) := exists y0 : real, ~ ((real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0)).
Definition term30 (x0 : real) := exists y0 : real, ~ ((real_add x0 y0) = (real_add y0 x0)).
Definition term121 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term135 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term236 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term209 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term173 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_add x0 (real_add x1 x2)) (real_add (real_add x0 x1) x2).
Definition term157 (x0 : real) (x1 : real) := @eq real (real_neg (real_sub (real_add x1 x0) (real_add x0 x1))).
Definition term153 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term9 (x0 : real) := @eq real (real_add (@neutral real real_add) x0).
Definition term182 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_add x1 x2) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))).
Definition term40 (x0 : real) (x1 : real) := ~ (forall y0 : real, (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0)).
Definition term22 (x0 : real) := ~ (forall y0 : real, (real_add x0 y0) = (real_add y0 x0)).
Definition term198 (x0 : real) := real_gt (real_neg (real_sub (real_add (real_of_num (NUMERAL 0)) x0) x0)) (real_of_num (NUMERAL 0)).
Definition term110 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term239 := (~ ((forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) /\ (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0)))) -> False.
Definition term205 := (exists y0 : real, exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((exists y0 : real, exists y1 : real, exists y2 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))).
Definition term86 := (exists y0 : real, exists y1 : real, ~ ((real_add y0 y1) = (real_add y1 y0))) \/ ((exists y0 : real, exists y1 : real, exists y2 : real, ~ ((real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2))) \/ (exists y0 : real, ~ ((real_add (real_of_num (NUMERAL 0)) y0) = y0))).
Definition term158 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_add x1 x0) (real_add x0 x1))).
Definition term35 (x0 : real) := forall y0 : real, (real_add x0 y0) = (real_add y0 x0).
Definition term228 := ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term148 := real_neg (real_of_num (NUMERAL 0)).
Definition term69 := ~ (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0).
Definition term25 (x0 : real) (x1 : real) := (fun y0 : real => (real_add x0 y0) = (real_add y0 x0)) x1.
Definition term119 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term114 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term26 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_add x0 y0) = (real_add y0 x0)) x1).
Definition term141 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term176 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_add x1 x2)).
Definition term85 := (~ (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0))) \/ (~ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) /\ (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0))).
Definition term203 := (exists y0 : real, exists y1 : real, exists y2 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term0 (a0 : Type') (x0 : type1400 a0) := (fun y0 : type1400 a0 => (@monoidal a0 y0) = ((forall y1 : a0, forall y2 : a0, (y0 y1 y2) = (y0 y2 y1)) /\ ((forall y1 : a0, forall y2 : a0, forall y3 : a0, (y0 y1 (y0 y2 y3)) = (y0 (y0 y1 y2) y3)) /\ (forall y1 : a0, (y0 (@neutral a0 y0) y1) = y1)))) x0.
Definition term24 (x0 : real) := fun y0 : real => (real_add x0 y0) = (real_add y0 x0).
Definition term188 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub (real_add x0 (real_add x1 x2)) (real_add (real_add x0 x1) x2)) (real_of_num (NUMERAL 0)).
Definition term131 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term109 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term117 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term207 (x0 : Prop) := exists y0 : real, x0.
Definition term222 := exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term154 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term88 := forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0).
Definition term82 := forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2).
Definition term64 (x0 : real) := forall y0 : real, forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1).
Definition term83 := or (~ (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0))).
Definition term77 := or (~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2))).
Definition term191 := exists y0 : real, exists y1 : real, exists y2 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term170 := exists y0 : real, exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term68 := exists y0 : real, exists y1 : real, exists y2 : real, ~ ((real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)).
Definition term59 (x0 : real) := exists y0 : real, exists y1 : real, ~ ((real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1)).
Definition term39 := exists y0 : real, exists y1 : real, ~ ((real_add y0 y1) = (real_add y1 y0)).
Definition term196 (x0 : real) := @eq real (real_neg (real_sub (real_add (real_of_num (NUMERAL 0)) x0) x0)).
Definition term152 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term224 := or (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term120 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term113 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term7 (x0 : real) := real_add (@neutral real real_add) x0.
Definition term47 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_add x0 (real_add x1 x2)) = (real_add (real_add x0 x1) x2)).
Definition term70 := exists y0 : real, ~ ((fun y1 : real => (real_add (real_of_num (NUMERAL 0)) y1) = y1) y0).
Definition term61 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, (real_add y1 (real_add y2 y3)) = (real_add (real_add y1 y2) y3)) y0).
Definition term52 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_add x0 (real_add y1 y2)) = (real_add (real_add x0 y1) y2)) y0).
Definition term41 (x0 : real) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => (real_add x0 (real_add x1 y1)) = (real_add (real_add x0 x1) y1)) y0).
Definition term32 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) y0).
Definition term23 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_add x0 y1) = (real_add y1 x0)) y0).
Definition term231 := real_lt (real_of_num (NUMERAL 0)).
Definition term66 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, (real_add y1 (real_add y2 y3)) = (real_add (real_add y1 y2) y3)) y0).
Definition term57 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_add x0 (real_add y1 y2)) = (real_add (real_add x0 y1) y2)) y0).
Definition term37 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) y0).
Definition term97 (x0 : real) (x1 : real) := real_add (real_add x0 x1).
Definition term71 (x0 : real) := (fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term19 := (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) /\ (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0)).
Definition term3 := (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) /\ (forall y0 : real, (real_add (@neutral real real_add) y0) = y0)).
Definition term2 (x0 : type1627) := (forall y0 : real, forall y1 : real, (x0 y0 y1) = (x0 y1 y0)) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (x0 y0 (x0 y1 y2)) = (x0 (x0 y0 y1) y2)) /\ (forall y0 : real, (x0 (@neutral real x0) y0) = y0)).
Definition term138 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term42 (x0 : real) (x1 : real) := fun y0 : real => (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0).
Definition term194 (x0 : real) := real_sub (real_add (real_of_num (NUMERAL 0)) x0) x0.
Definition term134 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term127 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term166 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term111 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term171 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_sub (real_add x0 (real_add x1 x2)) (real_add (real_add x0 x1) x2)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_add x0 (real_add x1 x2)) (real_add (real_add x0 x1) x2))) (real_of_num (NUMERAL 0))).
Definition term89 (x0 : real) (x1 : real) := (real_gt (real_sub (real_add x1 x0) (real_add x0 x1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_add x1 x0) (real_add x0 x1))) (real_of_num (NUMERAL 0))).
Definition term210 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term226 := (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term60 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)).
Definition term51 (x0 : real) := ~ (forall y0 : real, forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1)).
Definition term31 := ~ (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)).
Definition term238 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term149 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term177 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x1 x2)).
Definition term201 (x0 : real) := or (real_gt (real_sub (real_add (real_of_num (NUMERAL 0)) x0) x0) (real_of_num (NUMERAL 0))).
Definition term55 (x0 : real) (x1 : real) := forall y0 : real, (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0).
Definition term74 := fun y0 : real => ~ ((fun y1 : real => (real_add (real_of_num (NUMERAL 0)) y1) = y1) y0).
Definition term116 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term95 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term211 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term186 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_neg (real_sub (real_add x0 (real_add x1 x2)) (real_add (real_add x0 x1) x2))) (real_of_num (NUMERAL 0)).
Definition term160 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_add x1 x0) (real_add x0 x1))) (real_of_num (NUMERAL 0)).
Definition term161 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term233 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term214 := fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term145 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term5 := real_add (@neutral real real_add).
Definition term65 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) x0).
Definition term36 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) x0).
Definition term128 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term169 := fun y0 : real => exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term14 := forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0.
Definition term13 := forall y0 : real, (real_add (@neutral real real_add) y0) = y0.
Definition term76 := exists y0 : real, ~ ((real_add (real_of_num (NUMERAL 0)) y0) = y0).
Definition term172 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_add x0 (real_add x1 x2)).
Definition term27 (x0 : real) (x1 : real) := ~ ((real_add x1 x0) = (real_add x0 x1)).
Definition term220 := @eq Prop (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term219 := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0)).
Definition term183 (x0 : real) (x1 : real) (x2 : real) := real_neg (real_sub (real_add x0 (real_add x1 x2)) (real_add (real_add x0 x1) x2)).
Definition term53 (x0 : real) := fun y0 : real => forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1).
Definition term33 := fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0).
Definition term21 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term185 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_neg (real_sub (real_add x0 (real_add x1 x2)) (real_add (real_add x0 x1) x2))).
Definition term46 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0)) x2).
Definition term43 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0)) x2.
Definition term200 (x0 : real) := real_gt (real_sub (real_add (real_of_num (NUMERAL 0)) x0) x0) (real_of_num (NUMERAL 0)).
Definition term34 (x0 : real) := (fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) x0.
Definition term124 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term235 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term192 (x0 : real) := (real_gt (real_sub (real_add (real_of_num (NUMERAL 0)) x0) x0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_add (real_of_num (NUMERAL 0)) x0) x0)) (real_of_num (NUMERAL 0))).
Definition term118 := S (Nat.add 0 0).
Definition term150 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term93 (x0 : real) (x1 : real) := real_add (real_add x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1)).
Definition term102 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term87 := ~ ((forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) /\ (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0))).
Definition term96 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term162 (x0 : real) (x1 : real) := real_gt (real_sub (real_add x1 x0) (real_add x0 x1)).
Definition term130 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term184 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_neg (real_sub (real_add x0 (real_add x1 x2)) (real_add (real_add x0 x1) x2))).
Definition term136 := real_mul (real_of_num (NUMERAL 0)).
Definition term81 := ~ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) /\ (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0)).
Definition term230 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term54 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1)) x1.
Definition term100 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term91 (x0 : real) (x1 : real) := real_sub (real_add x1 x0) (real_add x0 x1).
Definition term206 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term122 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term58 (x0 : real) := fun y0 : real => exists y1 : real, ~ ((real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1)).
Definition term38 := fun y0 : real => exists y1 : real, ~ ((real_add y0 y1) = (real_add y1 y0)).
Definition term218 := fun y0 : real => ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term140 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term99 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term105 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term227 := or ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term212 := exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term167 := fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term44 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add x1 x2).
Definition term10 (x0 : real) := @eq real (real_add (real_of_num (NUMERAL 0)) x0).
Definition term129 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term75 := fun y0 : real => ~ ((real_add (real_of_num (NUMERAL 0)) y0) = y0).
Definition term217 (x0 : real) := ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term62 := fun y0 : real => forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2).
Definition term56 (x0 : real) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1)) x1).
Definition term190 := fun y0 : real => exists y1 : real, exists y2 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term67 := fun y0 : real => exists y1 : real, exists y2 : real, ~ ((real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)).
Definition term17 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) /\ (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0).
Definition term16 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) /\ (forall y0 : real, (real_add (@neutral real real_add) y0) = y0).
Definition term155 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term193 (x0 : real) := real_sub (real_add (real_of_num (NUMERAL 0)) x0).
Definition term125 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term92 (x0 : real) (x1 : real) := real_sub (real_add x0 x1) (real_add x0 x1).
Definition term142 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term8 (x0 : real) := real_add (real_of_num (NUMERAL 0)) x0.
Definition term139 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term104 := real_of_num (NUMERAL (BIT1 0)).
Definition term178 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term240 := ((~ ((forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) /\ (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0)))) -> False) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) /\ (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0)).
Definition term179 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)).
Definition term229 := ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ (((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))).
Definition term72 (x0 : real) := ~ ((fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0) x0).
Definition term73 (x0 : real) := ~ ((real_add (real_of_num (NUMERAL 0)) x0) = x0).
Definition term221 := fun y0 : real => (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term80 := (exists y0 : real, exists y1 : real, exists y2 : real, ~ ((real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2))) \/ (exists y0 : real, ~ ((real_add (real_of_num (NUMERAL 0)) y0) = y0)).
Definition term144 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term79 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2))) \/ (~ (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0)).
Definition term29 (x0 : real) := fun y0 : real => ~ ((real_add x0 y0) = (real_add y0 x0)).
Definition term174 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_add x0 (real_add x1 x2)) (real_add x0 (real_add x1 x2)).
Definition term48 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (real_add x0 (real_add x1 y1)) = (real_add (real_add x0 x1) y1)) y0).
Definition term28 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_add x0 y1) = (real_add y1 x0)) y0).
Definition term234 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term181 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 (real_add x1 x2)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))).
Definition term147 (x0 : real) (x1 : real) := real_neg (real_sub (real_add x1 x0) (real_add x0 x1)).
Definition term187 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub (real_add x0 (real_add x1 x2)) (real_add (real_add x0 x1) x2)).
Definition term165 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term123 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term216 (x0 : real) := or ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term146 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term199 (x0 : real) := real_gt (real_sub (real_add (real_of_num (NUMERAL 0)) x0) x0).
Definition term45 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 x1) x2.
Definition term232 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term112 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term103 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term180 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 (real_add x1 x2)).
Definition term151 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term90 (x0 : real) (x1 : real) := real_sub (real_add x0 x1).
Definition term156 := real_div (real_of_num (NUMERAL 0)).
Definition term6 := real_add (real_of_num (NUMERAL 0)).
Definition term225 := or (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term63 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) x0.
Definition term204 := or (exists y0 : real, exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term202 := or (exists y0 : real, exists y1 : real, exists y2 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term84 := or (exists y0 : real, exists y1 : real, ~ ((real_add y0 y1) = (real_add y1 y0))).
Definition term78 := or (exists y0 : real, exists y1 : real, exists y2 : real, ~ ((real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2))).
Definition term208 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term137 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term175 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 (real_add x1 x2)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_add x1 x2))).
Definition term98 (x0 : real) (x1 : real) := real_add (real_add x0 x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term106 := NUMERAL (BIT1 0).
Definition term213 := (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term168 := exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term12 := fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0.
Definition term11 := fun y0 : real => (real_add (@neutral real real_add) y0) = y0.
Definition term101 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term223 := exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term237 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term159 := real_gt (real_of_num (NUMERAL 0)).
