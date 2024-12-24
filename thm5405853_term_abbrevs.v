Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term198 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term266 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term39 (x0 : nat) := ~ (Peano.le x0 (NUMERAL 0)).
Definition term279 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term222 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term134 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term316 (x0 : nat) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) -> ((int_of_num x0) = (int_of_num (NUMERAL 0))) \/ ((~ (int_le (int_of_num x0) (int_of_num x1))) \/ (~ (int_le (int_of_num x1) (int_of_num (NUMERAL 0))))).
Definition term146 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term15 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (forall y0 : a0, x1 y0).
Definition term190 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1).
Definition term109 := real_add (real_of_int (int_of_num (NUMERAL 0))).
Definition term224 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term188 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term259 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term179 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term260 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term62 (x0 : int) (x1 : int) := ~ ((x0 = (int_of_num (NUMERAL 0))) \/ ((~ (int_le x0 x1)) \/ (~ (int_le x1 (int_of_num (NUMERAL 0)))))).
Definition term133 (x0 : nat) := real_neg (real_of_num x0).
Definition term173 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term310 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term77 := real_of_int (int_of_num (NUMERAL 0)).
Definition term126 (x0 : Prop) := ~ (~ x0).
Definition term78 := real_of_num (NUMERAL 0).
Definition term206 (x0 : int) (x1 : int) := (real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0))))).
Definition term13 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 (NUMERAL 0)))).
Definition term72 (x0 : int) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> (x0 = (int_of_num (NUMERAL 0))) \/ ((~ (int_le x0 x1)) \/ (~ (int_le x1 (int_of_num (NUMERAL 0)))))).
Definition term86 (x0 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)).
Definition term106 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term31 := int_of_num (NUMERAL 0).
Definition term83 (x0 : int) (x1 : int) := (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term313 (x0 : int) (x1 : int) := ((~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ ((real_le (real_of_int x0) (real_of_int x1)) /\ (real_le (real_of_int x1) (real_of_num (NUMERAL 0))))))))) -> False) -> ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ ((real_le (real_of_int x0) (real_of_int x1)) /\ (real_le (real_of_int x1) (real_of_num (NUMERAL 0))))))).
Definition term61 (x0 : int) (x1 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) /\ ((int_le x0 x1) /\ (int_le x1 (int_of_num (NUMERAL 0)))).
Definition term258 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term262 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term176 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term124 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ ((real_le (real_of_int x0) (real_of_int x1)) /\ (real_le (real_of_int x1) (real_of_num (NUMERAL 0))))).
Definition term192 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x0) (real_of_int x1)).
Definition term191 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term275 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term302 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term290 (x0 : int) (x1 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))).
Definition term197 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term201 (x0 : int) (x1 : int) := and (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))).
Definition term16 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 \/ (x1 y0).
Definition term246 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term47 (x0 : int) (x1 : int) := ~ (~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> (x0 = (int_of_num (NUMERAL 0))) \/ ((~ (int_le x0 x1)) \/ (~ (int_le x1 (int_of_num (NUMERAL 0))))))).
Definition term141 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term163 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term65 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ (~ ((x0 = (int_of_num (NUMERAL 0))) \/ ((~ (int_le x0 x1)) \/ (~ (int_le x1 (int_of_num (NUMERAL 0))))))).
Definition term178 (x0 : int) := real_sub (real_of_int x0) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term251 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term91 (x0 : int) := real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term67 (x0 : int) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x1) -> (x0 = (int_of_num (NUMERAL 0))) \/ ((~ (int_le x0 x1)) \/ (~ (int_le x1 (int_of_num (NUMERAL 0)))))).
Definition term184 (x0 : int) := real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term120 (x0 : int) (x1 : int) := (real_le (real_of_int x0) (real_of_int x1)) /\ (real_le (real_of_int x1) (real_of_num (NUMERAL 0))).
Definition term125 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ ((real_le (real_of_int x0) (real_of_int x1)) /\ (real_le (real_of_int x1) (real_of_num (NUMERAL 0)))))).
Definition term155 (x0 : int) := real_ge (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term6 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 (NUMERAL 0))).
Definition term186 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term111 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term23 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 (NUMERAL 0)))) y0.
Definition term37 (x0 : nat) (x1 : nat) := or (~ (int_le (int_of_num x0) (int_of_num x1))).
Definition term280 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term35 (x0 : nat) (x1 : nat) := ~ (int_le (int_of_num x0) (int_of_num x1)).
Definition term119 (x0 : int) (x1 : int) := and (real_le (real_of_int x0) (real_of_int x1)).
Definition term256 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term255 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term160 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term132 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term20 (x0 : nat) := forall y0 : nat, (x0 = (NUMERAL 0)) \/ ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 (NUMERAL 0)))) y0).
Definition term69 (x0 : int) (x1 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ ((~ (int_le x0 x1)) \/ (~ (int_le x1 (int_of_num (NUMERAL 0))))).
Definition term81 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term115 (x0 : int) := (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term285 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term238 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term189 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term154 (x0 : int) := real_ge (real_of_int x0).
Definition term1 (x0 : nat) := fun y0 : nat => ~ ((Peano.le x0 y0) /\ (Peano.le y0 (NUMERAL 0))).
Definition term172 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term167 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term57 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term136 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term3 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term208 (x0 : int) (x1 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0))))).
Definition term273 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term71 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_le (int_of_num (NUMERAL 0)) x1) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ ((int_le x0 x1) /\ (int_le x1 (int_of_num (NUMERAL 0)))))).
Definition term170 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term153 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term225 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term92 (x0 : int) := real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term148 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term274 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term205 (x0 : int) := and (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term140 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term278 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term8 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 (NUMERAL 0))).
Definition term17 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (forall y0 : nat, x1 y0).
Definition term216 (x0 : int) (x1 : int) := (real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0))))).
Definition term215 (x0 : int) (x1 : int) := (real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0))))).
Definition term257 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term63 (x0 : int) (x1 : int) := (~ (int_le x0 x1)) \/ (~ (int_le x1 (int_of_num (NUMERAL 0)))).
Definition term315 (x0 : nat) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x0)) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) -> ((int_of_num x0) = (int_of_num (NUMERAL 0))) \/ ((~ (int_le (int_of_num x0) (int_of_num x1))) \/ (~ (int_le (int_of_num x1) (int_of_num (NUMERAL 0))))).
Definition term254 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term183 (x0 : int) := real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term112 := real_le (real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term152 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term187 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)).
Definition term80 := real_le (real_of_num (NUMERAL 0)).
Definition term89 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term281 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term104 (x0 : int) := int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term14 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term185 (x0 : int) := or (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term157 (x0 : int) := real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term288 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term12 (x0 : nat) := (~ (~ (x0 = (NUMERAL 0)))) \/ (forall y0 : nat, ~ ((Peano.le x0 y0) /\ (Peano.le y0 (NUMERAL 0)))).
Definition term220 := real_lt (real_of_num (NUMERAL 0)).
Definition term97 (x0 : int) := real_add (real_of_int x0).
Definition term45 (x0 : nat) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) x0.
Definition term307 (x0 : int) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term295 (x0 : int) (x1 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term127 (x0 : int) (x1 : int) := ~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ ((real_le (real_of_int x0) (real_of_int x1)) /\ (real_le (real_of_int x1) (real_of_num (NUMERAL 0)))))))).
Definition term309 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term297 (x0 : int) (x1 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term103 (x0 : int) := or (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term283 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term26 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) \/ ((fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 (NUMERAL 0)))) x1).
Definition term34 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term22 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 (NUMERAL 0)))) y0.
Definition term250 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term76 (x0 : nat) := real_of_int (int_of_num x0).
Definition term230 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term4 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> forall y0 : nat, ~ ((Peano.le x0 y0) /\ (Peano.le y0 (NUMERAL 0))).
Definition term261 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term147 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term54 (x0 : int) (x1 : int) := (~ (~ (int_le x0 x1))) /\ (~ (~ (int_le x1 (int_of_num (NUMERAL 0))))).
Definition term90 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term60 (x0 : int) (x1 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((~ (int_le x0 x1)) \/ (~ (int_le x1 (int_of_num (NUMERAL 0)))))).
Definition term87 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num (NUMERAL 0))).
Definition term252 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term107 := real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term139 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term116 (x0 : int) := real_le (real_of_int x0) (real_of_int (int_of_num (NUMERAL 0))).
Definition term282 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term168 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term219 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term174 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term10 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term41 (x0 : nat) (x1 : nat) := (~ (int_le (int_of_num x0) (int_of_num x1))) \/ (~ (int_le (int_of_num x1) (int_of_num (NUMERAL 0)))).
Definition term121 (x0 : int) := and ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term249 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0).
Definition term11 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term100 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term196 (x0 : int) := real_sub (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term165 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term102 (x0 : int) := or (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))).
Definition term29 (x0 : nat) := fun y0 : nat => (x0 = (NUMERAL 0)) \/ ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 (NUMERAL 0)))).
Definition term235 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term200 (x0 : int) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term247 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term244 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term233 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term38 (x0 : nat) := int_le (int_of_num x0) (int_of_num (NUMERAL 0)).
Definition term195 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term114 (x0 : int) := real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term73 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> (x0 = (int_of_num (NUMERAL 0))) \/ ((~ (int_le x0 x1)) \/ (~ (int_le x1 (int_of_num (NUMERAL 0))))).
Definition term169 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term181 (x0 : int) := real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term306 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term144 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term271 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term118 (x0 : int) := real_le (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term304 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term292 (x0 : int) (x1 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1))) (real_of_num (NUMERAL 0)).
Definition term2 (x0 : nat) := forall y0 : nat, ~ ((Peano.le x0 y0) /\ (Peano.le y0 (NUMERAL 0))).
Definition term182 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term193 (x0 : int) (x1 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)).
Definition term270 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)).
Definition term227 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term277 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term88 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term243 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term226 := S (Nat.add 0 0).
Definition term137 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term85 (x0 : int) := (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))) \/ (int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term194 (x0 : int) (x1 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0)).
Definition term135 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term214 (x0 : int) (x1 : int) := ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0))))))) \/ ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0))))))).
Definition term210 (x0 : int) (x1 : int) := ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0)))))) \/ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0)))))).
Definition term299 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term298 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term162 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term55 (x0 : int) (x1 : int) := (int_le x0 x1) /\ (int_le x1 (int_of_num (NUMERAL 0))).
Definition term237 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)).
Definition term58 (x0 : int) := ~ (int_le x0 (int_of_num (NUMERAL 0))).
Definition term232 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term9 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 (NUMERAL 0))).
Definition term305 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term105 (x0 : int) := real_le (real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term263 := real_mul (real_of_num (NUMERAL 0)).
Definition term212 (x0 : int) (x1 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0)))).
Definition term211 (x0 : int) (x1 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0)))).
Definition term52 (x0 : int) (x1 : int) := and (~ (~ (int_le x0 x1))).
Definition term156 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term84 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term36 (x0 : nat) (x1 : nat) := or (~ (Peano.le x0 x1)).
Definition term99 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term51 (x0 : int) := int_le x0 (int_of_num (NUMERAL 0)).
Definition term21 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 (NUMERAL 0)))) x1.
Definition term177 (x0 : int) := real_sub (real_of_int x0).
Definition term46 (x0 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term19 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 (NUMERAL 0)))) y0).
Definition term142 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term265 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term66 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ ((~ (x0 = (int_of_num (NUMERAL 0)))) /\ ((int_le x0 x1) /\ (int_le x1 (int_of_num (NUMERAL 0))))).
Definition term113 := real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term82 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term161 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term308 (x0 : int) := ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term303 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term296 (x0 : int) (x1 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term291 (x0 : int) (x1 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1))) (real_of_num (NUMERAL 0)).
Definition term286 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term239 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term64 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term203 (x0 : int) := and ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term44 (x0 : nat) := forall y0 : nat, ((int_of_num x0) = (int_of_num (NUMERAL 0))) \/ ((~ (int_le (int_of_num x0) (int_of_num y0))) \/ (~ (int_le (int_of_num y0) (int_of_num (NUMERAL 0))))).
Definition term30 (x0 : nat) := forall y0 : nat, (x0 = (NUMERAL 0)) \/ ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 (NUMERAL 0)))).
Definition term180 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term166 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term294 (x0 : int) (x1 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1))).
Definition term129 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term74 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term53 (x0 : int) (x1 : int) := and (int_le x0 x1).
Definition term311 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term301 (x0 : int) (x1 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term175 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term70 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (~ ((int_le (int_of_num (NUMERAL 0)) x1) -> (x0 = (int_of_num (NUMERAL 0))) \/ ((~ (int_le x0 x1)) \/ (~ (int_le x1 (int_of_num (NUMERAL 0))))))).
Definition term56 (x0 : int) (x1 : int) := ~ ((~ (int_le x0 x1)) \/ (~ (int_le x1 (int_of_num (NUMERAL 0))))).
Definition term101 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term149 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term245 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term234 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term50 (x0 : int) := ~ (~ (int_le x0 (int_of_num (NUMERAL 0)))).
Definition term130 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term43 (x0 : nat) := fun y0 : nat => ((int_of_num x0) = (int_of_num (NUMERAL 0))) \/ ((~ (int_le (int_of_num x0) (int_of_num y0))) \/ (~ (int_le (int_of_num y0) (int_of_num (NUMERAL 0))))).
Definition term145 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term151 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term229 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term95 := real_of_num (NUMERAL (BIT1 0)).
Definition term228 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term199 (x0 : int) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term314 (x0 : int) (x1 : int) := ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ ((real_le (real_of_int x0) (real_of_int x1)) /\ (real_le (real_of_int x1) (real_of_num (NUMERAL 0))))))).
Definition term75 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term269 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term18 (x0 : Prop) (x1 : nat -> Prop) := forall y0 : nat, x0 \/ (x1 y0).
Definition term25 (x0 : nat) := @eq Prop ((x0 = (NUMERAL 0)) \/ (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 (NUMERAL 0))))).
Definition term24 (x0 : nat) := @eq Prop ((x0 = (NUMERAL 0)) \/ (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 (NUMERAL 0)))) y0)).
Definition term42 (x0 : nat) (x1 : nat) := ((int_of_num x0) = (int_of_num (NUMERAL 0))) \/ ((~ (int_le (int_of_num x0) (int_of_num x1))) \/ (~ (int_le (int_of_num x1) (int_of_num (NUMERAL 0))))).
Definition term123 (x0 : int) := and (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term242 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term241 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term48 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> (x0 = (int_of_num (NUMERAL 0))) \/ ((~ (int_le x0 x1)) \/ (~ (int_le x1 (int_of_num (NUMERAL 0))))).
Definition term171 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term276 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term223 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term213 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0)))))) \/ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0))))))).
Definition term209 (x0 : int) (x1 : int) := (real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0)))))).
Definition term248 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term236 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0).
Definition term40 (x0 : nat) := ~ (int_le (int_of_num x0) (int_of_num (NUMERAL 0))).
Definition term289 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term33 (x0 : nat) (x1 : nat) := int_le (int_of_num x0) (int_of_num x1).
Definition term94 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term300 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term117 (x0 : int) := real_le (real_of_int x0).
Definition term143 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term68 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term98 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term202 (x0 : int) (x1 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0))).
Definition term267 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term5 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term27 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 (NUMERAL 0)))).
Definition term284 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0)))))).
Definition term217 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0)))))).
Definition term207 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0)))))).
Definition term159 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term28 (x0 : nat) := fun y0 : nat => (x0 = (NUMERAL 0)) \/ ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 (NUMERAL 0)))) y0).
Definition term221 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term253 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term131 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term204 (x0 : int) (x1 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_num (NUMERAL 0)))).
Definition term108 := real_add (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term79 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term272 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term138 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term150 := real_div (real_of_num (NUMERAL 0)).
Definition term7 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term110 := real_add (real_of_num (NUMERAL 0)).
Definition term312 (x0 : int) (x1 : int) := (~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ ((real_le (real_of_int x0) (real_of_int x1)) /\ (real_le (real_of_int x1) (real_of_num (NUMERAL 0))))))))) -> False.
Definition term122 (x0 : int) (x1 : int) := ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ ((real_le (real_of_int x0) (real_of_int x1)) /\ (real_le (real_of_int x1) (real_of_num (NUMERAL 0)))).
Definition term158 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term264 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term93 := int_of_num (NUMERAL (BIT1 0)).
Definition term268 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)).
Definition term293 (x0 : int) (x1 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x1)).
Definition term49 (x0 : int) (x1 : int) := ~ (~ (int_le x0 x1)).
Definition term96 := NUMERAL (BIT1 0).
Definition term59 (x0 : int) := and (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term218 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term164 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term287 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term240 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term0 (x0 : nat) (x1 : nat) := ~ ((Peano.le x0 x1) /\ (Peano.le x1 (NUMERAL 0))).
Definition term231 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term128 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term32 (x0 : nat) := or ((int_of_num x0) = (int_of_num (NUMERAL 0))).
