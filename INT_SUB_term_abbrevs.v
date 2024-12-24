Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term220 := or (exists y0 : int, exists y1 : int, real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term114 := or (exists y0 : int, exists y1 : int, real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1)))).
Definition term45 (x0 : int) (x1 : int) := real_le (real_add (real_sub (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term16 := fun y0 : int => forall y1 : int, (int_sub y0 y1) = (int_add y0 (int_neg y1)).
Definition term200 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term233 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term116 := exists y0 : int, (fun y1 : int => exists y2 : int, real_le (real_add (real_add (real_of_int y1) (real_neg (real_of_int y2))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y1) (real_of_int y2))) y0.
Definition term111 := exists y0 : int, (fun y1 : int => exists y2 : int, real_le (real_add (real_sub (real_of_int y1) (real_of_int y2)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y1) (real_neg (real_of_int y2)))) y0.
Definition term3 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term139 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term2 (x0 : int -> Prop) := ~ (all x0).
Definition term150 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term59 (x0 : int) (x1 : int) := real_add (real_of_int (int_add x0 (int_neg x1))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term175 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term35 (x0 : int) (x1 : int) := real_of_int (int_sub x0 x1).
Definition term183 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term36 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term190 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term191 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term95 (x0 : int) := exists y0 : int, real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int y0))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int y0)).
Definition term138 (x0 : nat) := real_neg (real_of_num x0).
Definition term204 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term71 (x0 : Prop) := ~ (~ x0).
Definition term182 := real_of_num (NUMERAL 0).
Definition term13 (x0 : int) := exists y0 : int, ~ ((int_sub x0 y0) = (int_add x0 (int_neg y0))).
Definition term76 (x0 : int -> Prop) (x1 : int -> Prop) := (exists y0 : int, x0 y0) \/ (exists y0 : int, x1 y0).
Definition term213 := exists y0 : int, real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term159 (x0 : int) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term238 := (~ (~ (exists y0 : int, exists y1 : int, (real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1)))) \/ (real_le (real_add (real_add (real_of_int y0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y0) (real_of_int y1)))))) -> False.
Definition term24 (x0 : int) (x1 : int) := (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term83 (x0 : int) (x1 : int) := (fun y0 : int => real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int y0))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int y0))) x1.
Definition term189 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term193 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term124 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term229 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term66 (x0 : int) (x1 : int) := (real_le (real_add (real_sub (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int x1)))) \/ (real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int x1))).
Definition term107 := fun y0 : int => ((fun y1 : int => exists y2 : int, real_le (real_add (real_sub (real_of_int y1) (real_of_int y2)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y1) (real_neg (real_of_int y2)))) y0) \/ ((fun y1 : int => exists y2 : int, real_le (real_add (real_add (real_of_int y1) (real_neg (real_of_int y2))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y1) (real_of_int y2))) y0).
Definition term17 (x0 : int) := (fun y0 : int => forall y1 : int, (int_sub y0 y1) = (int_add y0 (int_neg y1))) x0.
Definition term125 (x0 : int) (x1 : int) := real_sub (real_add (real_of_int x0) (real_neg (real_of_int x1))).
Definition term144 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term54 (x0 : int) (x1 : int) := or (real_le (real_add (real_sub (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int x1)))).
Definition term64 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term177 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term11 (x0 : int) := fun y0 : int => ~ ((fun y1 : int => (int_sub x0 y1) = (int_add x0 (int_neg y1))) y0).
Definition term127 (x0 : int) (x1 : int) := real_sub (real_add (real_of_int x0) (real_neg (real_of_int x1))) (real_add (real_sub (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term56 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add x0 (int_neg x1)) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_sub x0 x1)).
Definition term234 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term187 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term181 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term65 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int x1)).
Definition term47 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int (int_neg x1)).
Definition term199 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term120 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term134 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term67 (x0 : int) := fun y0 : int => (real_le (real_add (real_sub (real_of_int x0) (real_of_int y0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y0)))) \/ (real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int y0))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int y0))).
Definition term63 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add x0 (int_neg x1)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term154 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term140 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term32 (x0 : int) (x1 : int) := real_of_int (int_add (int_sub x0 x1) (int_of_num (NUMERAL (BIT1 0)))).
Definition term226 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term38 (x0 : int) (x1 : int) := real_add (real_sub (real_of_int x0) (real_of_int x1)).
Definition term19 (x0 : int) := ~ ((fun y0 : int => forall y1 : int, (int_sub y0 y1) = (int_add y0 (int_neg y1))) x0).
Definition term171 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term90 (x0 : int) := exists y0 : int, real_le (real_add (real_sub (real_of_int x0) (real_of_int y0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y0))).
Definition term217 (x0 : int) (x1 : int) := real_sub (real_sub (real_of_int x0) (real_of_int x1)).
Definition term82 (x0 : int) (x1 : int) := or ((fun y0 : int => real_le (real_add (real_sub (real_of_int x0) (real_of_int y0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y0)))) x1).
Definition term185 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term68 (x0 : int) := exists y0 : int, (real_le (real_add (real_sub (real_of_int x0) (real_of_int y0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y0)))) \/ (real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int y0))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int y0))).
Definition term228 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term160 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term105 (x0 : int) := (fun y0 : int => exists y1 : int, real_le (real_add (real_add (real_of_int y0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y0) (real_of_int y1))) x0.
Definition term103 (x0 : int) := (fun y0 : int => exists y1 : int, real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1)))) x0.
Definition term232 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term46 (x0 : int) (x1 : int) := real_of_int (int_add x0 (int_neg x1)).
Definition term188 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term180 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term57 (x0 : int) (x1 : int) := int_add (int_add x0 (int_neg x1)) (int_of_num (NUMERAL (BIT1 0))).
Definition term227 := real_le (real_of_num (NUMERAL 0)).
Definition term30 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term235 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term97 := fun y0 : int => (exists y1 : int, real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1)))) \/ (exists y1 : int, real_le (real_add (real_add (real_of_int y0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y0) (real_of_int y1))).
Definition term62 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))).
Definition term130 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term98 := exists y0 : int, (exists y1 : int, real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1)))) \/ (exists y1 : int, real_le (real_add (real_add (real_of_int y0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y0) (real_of_int y1))).
Definition term6 (x0 : int) := fun y0 : int => (int_sub x0 y0) = (int_add x0 (int_neg y0)).
Definition term50 (x0 : int) := real_add (real_of_int x0).
Definition term237 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term176 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term39 (x0 : nat) := real_of_int (int_of_num x0).
Definition term196 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term192 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term151 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term162 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term31 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term239 := ((~ (~ (exists y0 : int, exists y1 : int, (real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1)))) \/ (real_le (real_add (real_add (real_of_int y0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y0) (real_of_int y1)))))) -> False) -> ~ (exists y0 : int, exists y1 : int, (real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1)))) \/ (real_le (real_add (real_add (real_of_int y0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y0) (real_of_int y1)))).
Definition term178 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term28 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_sub x0 x1) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_add x0 (int_neg x1))).
Definition term221 := (exists y0 : int, exists y1 : int, real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (exists y0 : int, exists y1 : int, real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term118 := (exists y0 : int, exists y1 : int, real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1)))) \/ (exists y0 : int, exists y1 : int, real_le (real_add (real_add (real_of_int y0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y0) (real_of_int y1))).
Definition term236 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term155 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term100 := (exists y0 : int, (fun y1 : int => exists y2 : int, real_le (real_add (real_sub (real_of_int y1) (real_of_int y2)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y1) (real_neg (real_of_int y2)))) y0) \/ (exists y0 : int, (fun y1 : int => exists y2 : int, real_le (real_add (real_add (real_of_int y1) (real_neg (real_of_int y2))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y1) (real_of_int y2))) y0).
Definition term78 (x0 : int) := (exists y0 : int, (fun y1 : int => real_le (real_add (real_sub (real_of_int x0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y1)))) y0) \/ (exists y0 : int, (fun y1 : int => real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int y1))) y0).
Definition term184 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term169 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term206 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0).
Definition term109 := @eq Prop (exists y0 : int, (exists y1 : int, real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1)))) \/ (exists y1 : int, real_le (real_add (real_add (real_of_int y0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y0) (real_of_int y1)))).
Definition term108 := @eq Prop (exists y0 : int, ((fun y1 : int => exists y2 : int, real_le (real_add (real_sub (real_of_int y1) (real_of_int y2)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y1) (real_neg (real_of_int y2)))) y0) \/ ((fun y1 : int => exists y2 : int, real_le (real_add (real_add (real_of_int y1) (real_neg (real_of_int y2))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y1) (real_of_int y2))) y0)).
Definition term87 (x0 : int) := @eq Prop (exists y0 : int, (real_le (real_add (real_sub (real_of_int x0) (real_of_int y0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y0)))) \/ (real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int y0))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int y0)))).
Definition term86 (x0 : int) := @eq Prop (exists y0 : int, ((fun y1 : int => real_le (real_add (real_sub (real_of_int x0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y1)))) y0) \/ ((fun y1 : int => real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int y1))) y0)).
Definition term209 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_neg (real_of_int x1))) (real_add (real_sub (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term7 (x0 : int) (x1 : int) := (fun y0 : int => (int_sub x0 y0) = (int_add x0 (int_neg y0))) x1.
Definition term202 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term121 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term96 (x0 : int) := (exists y0 : int, real_le (real_add (real_sub (real_of_int x0) (real_of_int y0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y0)))) \/ (exists y0 : int, real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int y0))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int y0))).
Definition term174 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term173 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term27 (x0 : int) (x1 : int) := int_le (int_add (int_sub x0 x1) (int_of_num (NUMERAL (BIT1 0)))) (int_add x0 (int_neg x1)).
Definition term152 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term128 (x0 : int) (x1 : int) := real_sub (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term216 (x0 : int) (x1 : int) := real_ge (real_sub (real_sub (real_of_int x0) (real_of_int x1)) (real_add (real_add (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term119 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_neg (real_of_int x1))) (real_add (real_sub (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term4 (x0 : int) := ~ (forall y0 : int, (int_sub x0 y0) = (int_add x0 (int_neg y0))).
Definition term166 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term165 := real_div (real_of_num (NUMERAL (BIT1 0))).
Definition term94 (x0 : int) := exists y0 : int, (fun y1 : int => real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int y1))) y0.
Definition term89 (x0 : int) := exists y0 : int, (fun y1 : int => real_le (real_add (real_sub (real_of_int x0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y1)))) y0.
Definition term131 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term156 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term170 (x0 : int) := real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term1 := forall y0 : int, forall y1 : int, (int_sub y0 y1) = (int_add y0 (int_neg y1)).
Definition term148 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term210 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term33 (x0 : int) (x1 : int) := real_add (real_of_int (int_sub x0 x1)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term93 (x0 : int) := fun y0 : int => (fun y1 : int => real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int y1))) y0.
Definition term88 (x0 : int) := fun y0 : int => (fun y1 : int => real_le (real_add (real_sub (real_of_int x0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y1)))) y0.
Definition term231 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term186 := S (Nat.add 0 0).
Definition term141 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term218 (x0 : int) (x1 : int) := real_sub (real_sub (real_of_int x0) (real_of_int x1)) (real_add (real_add (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term0 := ~ (~ (forall y0 : int, forall y1 : int, (int_sub y0 y1) = (int_add y0 (int_neg y1)))).
Definition term172 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term132 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term143 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term225 := (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term79 (x0 : int) := fun y0 : int => real_le (real_add (real_sub (real_of_int x0) (real_of_int y0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y0))).
Definition term85 (x0 : int) := fun y0 : int => ((fun y1 : int => real_le (real_add (real_sub (real_of_int x0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y1)))) y0) \/ ((fun y1 : int => real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int y1))) y0).
Definition term219 (x0 : int) (x1 : int) := real_ge (real_sub (real_sub (real_of_int x0) (real_of_int x1)) (real_add (real_add (real_of_int x0) (real_neg (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term240 := ~ (exists y0 : int, exists y1 : int, (real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1)))) \/ (real_le (real_add (real_add (real_of_int y0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y0) (real_of_int y1)))).
Definition term194 := real_mul (real_of_num (NUMERAL 0)).
Definition term222 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term161 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term55 (x0 : int) (x1 : int) := int_le (int_add (int_add x0 (int_neg x1)) (int_of_num (NUMERAL (BIT1 0)))) (int_sub x0 x1).
Definition term164 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term51 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_neg (real_of_int x1)).
Definition term14 := ~ (forall y0 : int, forall y1 : int, (int_sub y0 y1) = (int_add y0 (int_neg y1))).
Definition term146 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term167 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term198 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term23 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term49 (x0 : int) := real_neg (real_of_int x0).
Definition term9 (x0 : int) (x1 : int) := ~ ((fun y0 : int => (int_sub x0 y0) = (int_add x0 (int_neg y0))) x1).
Definition term106 (x0 : int) := ((fun y0 : int => exists y1 : int, real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1)))) x0) \/ ((fun y0 : int => exists y1 : int, real_le (real_add (real_add (real_of_int y0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y0) (real_of_int y1))) x0).
Definition term137 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term158 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term153 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term26 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term163 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term8 (x0 : int) (x1 : int) := int_add x0 (int_neg x1).
Definition term104 (x0 : int) := or ((fun y0 : int => exists y1 : int, real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1)))) x0).
Definition term75 (x0 : int -> Prop) (x1 : int -> Prop) := exists y0 : int, (x0 y0) \/ (x1 y0).
Definition term84 (x0 : int) (x1 : int) := ((fun y0 : int => real_le (real_add (real_sub (real_of_int x0) (real_of_int y0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y0)))) x1) \/ ((fun y0 : int => real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int y0))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int y0))) x1).
Definition term25 (x0 : int) (x1 : int) := (int_le (int_add (int_sub x0 x1) (int_of_num (NUMERAL (BIT1 0)))) (int_add x0 (int_neg x1))) \/ (int_le (int_add (int_add x0 (int_neg x1)) (int_of_num (NUMERAL (BIT1 0)))) (int_sub x0 x1)).
Definition term149 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term129 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))))).
Definition term157 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term197 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term41 := real_of_num (NUMERAL (BIT1 0)).
Definition term92 (x0 : int) := or (exists y0 : int, real_le (real_add (real_sub (real_of_int x0) (real_of_int y0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y0)))).
Definition term208 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term126 (x0 : int) (x1 : int) := real_sub (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term99 := exists y0 : int, ((fun y1 : int => exists y2 : int, real_le (real_add (real_sub (real_of_int y1) (real_of_int y2)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y1) (real_neg (real_of_int y2)))) y0) \/ ((fun y1 : int => exists y2 : int, real_le (real_add (real_add (real_of_int y1) (real_neg (real_of_int y2))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y1) (real_of_int y2))) y0).
Definition term77 (x0 : int) := exists y0 : int, ((fun y1 : int => real_le (real_add (real_sub (real_of_int x0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y1)))) y0) \/ ((fun y1 : int => real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int y1))) y0).
Definition term212 := fun y0 : int => real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term133 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term81 (x0 : int) (x1 : int) := (fun y0 : int => real_le (real_add (real_sub (real_of_int x0) (real_of_int y0)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y0)))) x1.
Definition term21 := fun y0 : int => exists y1 : int, ~ ((int_sub y0 y1) = (int_add y0 (int_neg y1))).
Definition term43 (x0 : int) (x1 : int) := real_add (real_sub (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))).
Definition term230 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term61 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_neg (real_of_int x1))).
Definition term205 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term48 (x0 : int) := real_of_int (int_neg x0).
Definition term168 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0).
Definition term40 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term10 (x0 : int) (x1 : int) := ~ ((int_sub x0 x1) = (int_add x0 (int_neg x1))).
Definition term113 := or (exists y0 : int, (fun y1 : int => exists y2 : int, real_le (real_add (real_sub (real_of_int y1) (real_of_int y2)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y1) (real_neg (real_of_int y2)))) y0).
Definition term91 (x0 : int) := or (exists y0 : int, (fun y1 : int => real_le (real_add (real_sub (real_of_int x0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int y1)))) y0).
Definition term53 (x0 : int) (x1 : int) := or (int_le (int_add (int_sub x0 x1) (int_of_num (NUMERAL (BIT1 0)))) (int_add x0 (int_neg x1))).
Definition term147 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term15 := exists y0 : int, ~ ((fun y1 : int => forall y2 : int, (int_sub y1 y2) = (int_add y1 (int_neg y2))) y0).
Definition term5 (x0 : int) := exists y0 : int, ~ ((fun y1 : int => (int_sub x0 y1) = (int_add x0 (int_neg y1))) y0).
Definition term215 := exists y0 : int, exists y1 : int, real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term117 := exists y0 : int, exists y1 : int, real_le (real_add (real_add (real_of_int y0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y0) (real_of_int y1)).
Definition term112 := exists y0 : int, exists y1 : int, real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1))).
Definition term70 := exists y0 : int, exists y1 : int, (real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1)))) \/ (real_le (real_add (real_add (real_of_int y0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y0) (real_of_int y1))).
Definition term22 := exists y0 : int, exists y1 : int, ~ ((int_sub y0 y1) = (int_add y0 (int_neg y1))).
Definition term80 (x0 : int) := fun y0 : int => real_le (real_add (real_add (real_of_int x0) (real_neg (real_of_int y0))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int x0) (real_of_int y0)).
Definition term102 := fun y0 : int => exists y1 : int, real_le (real_add (real_add (real_of_int y0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y0) (real_of_int y1)).
Definition term101 := fun y0 : int => exists y1 : int, real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1))).
Definition term69 := fun y0 : int => exists y1 : int, (real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1)))) \/ (real_le (real_add (real_add (real_of_int y0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y0) (real_of_int y1))).
Definition term123 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term52 (x0 : int) (x1 : int) := real_le (real_add (real_sub (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_neg (real_of_int x1))).
Definition term122 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL (BIT1 0))).
Definition term18 (x0 : int) := forall y0 : int, (int_sub x0 y0) = (int_add x0 (int_neg y0)).
Definition term201 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term115 := fun y0 : int => (fun y1 : int => exists y2 : int, real_le (real_add (real_add (real_of_int y1) (real_neg (real_of_int y2))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y1) (real_of_int y2))) y0.
Definition term110 := fun y0 : int => (fun y1 : int => exists y2 : int, real_le (real_add (real_sub (real_of_int y1) (real_of_int y2)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y1) (real_neg (real_of_int y2)))) y0.
Definition term179 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term136 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term72 := ~ (~ (exists y0 : int, exists y1 : int, (real_le (real_add (real_sub (real_of_int y0) (real_of_int y1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int y0) (real_neg (real_of_int y1)))) \/ (real_le (real_add (real_add (real_of_int y0) (real_neg (real_of_int y1))) (real_of_num (NUMERAL (BIT1 0)))) (real_sub (real_of_int y0) (real_of_int y1))))).
Definition term214 := fun y0 : int => exists y1 : int, real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term211 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term29 (x0 : int) (x1 : int) := int_add (int_sub x0 x1) (int_of_num (NUMERAL (BIT1 0))).
Definition term142 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term203 := real_add (real_of_num (NUMERAL 0)).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term37 (x0 : int) (x1 : int) := real_add (real_of_int (int_sub x0 x1)).
Definition term44 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_sub x0 x1) (int_of_num (NUMERAL (BIT1 0))))).
Definition term135 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term195 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term224 := or (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term34 := int_of_num (NUMERAL (BIT1 0)).
Definition term60 (x0 : int) (x1 : int) := real_add (real_of_int (int_add x0 (int_neg x1))).
Definition term207 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)).
Definition term223 (x0 : Prop) := exists y0 : int, x0.
Definition term42 := NUMERAL (BIT1 0).
Definition term58 (x0 : int) (x1 : int) := real_of_int (int_add (int_add x0 (int_neg x1)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term12 (x0 : int) := fun y0 : int => ~ ((int_sub x0 y0) = (int_add x0 (int_neg y0))).
Definition term145 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term20 := fun y0 : int => ~ ((fun y1 : int => forall y2 : int, (int_sub y1 y2) = (int_add y1 (int_neg y2))) y0).
