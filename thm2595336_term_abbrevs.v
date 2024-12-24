Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term211 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term260 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term120 := real_le (real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num (NUMERAL 0))).
Definition term163 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term9 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (x0 = (int_add (int_mul x1 x3) x2)) /\ ((int_le (int_of_num (NUMERAL 0)) x2) /\ (int_lt x2 (int_abs x3))).
Definition term174 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term18 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => forall y1 : int, ((x1 = (int_add (int_mul x0 y0) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs y0)))) -> ((div x1 y0) = x0) /\ ((rem x1 y0) = y1)) x2.
Definition term5 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => forall y1 : int, ((x0 = (int_add (int_mul y0 x1) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs x1)))) -> ((div x0 x1) = y0) /\ ((rem x0 x1) = y1)) x2.
Definition term187 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term124 := real_add (real_of_int (int_of_num (NUMERAL 0))).
Definition term194 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term156 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term45 := @eq Prop ((forall y0 : int, (div y0 (int_of_num (NUMERAL (BIT1 0)))) = y0) /\ (forall y0 : int, (rem y0 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0)))).
Definition term44 := @eq Prop ((forall y0 : int, (fun y1 : int => (div y1 (int_of_num (NUMERAL (BIT1 0)))) = y1) y0) /\ (forall y0 : int, (fun y1 : int => (rem y1 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0))) y0)).
Definition term201 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term202 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term28 := fun y0 : int => (div y0 (int_of_num (NUMERAL (BIT1 0)))) = y0.
Definition term32 := fun y0 : int => (fun y1 : int => (div y1 (int_of_num (NUMERAL (BIT1 0)))) = y1) y0.
Definition term162 (x0 : nat) := real_neg (real_of_num x0).
Definition term98 := real_of_int (int_of_num (NUMERAL 0)).
Definition term148 (x0 : Prop) := ~ (~ x0).
Definition term99 := real_of_num (NUMERAL 0).
Definition term146 (x0 : int) := or ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term185 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term73 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)))).
Definition term121 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term39 := int_of_num (NUMERAL 0).
Definition term51 := fun y0 : int => ((div y0 (int_of_num (NUMERAL (BIT1 0)))) = y0) /\ ((rem y0 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0))).
Definition term129 := real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term68 (x0 : int) (x1 : int) := (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term17 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((y0 = (int_add (int_mul x0 y1) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y1)))) -> ((div y0 y1) = x0) /\ ((rem y0 y1) = y2)) x1.
Definition term3 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((x0 = (int_add (int_mul y1 y0) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y0)))) -> ((div x0 y0) = y1) /\ ((rem x0 y0) = y2)) x1.
Definition term91 (x0 : int) (x1 : int) := real_mul (real_of_int x0) (real_of_int x1).
Definition term200 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term204 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term218 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term62 (x0 : int) := (~ (x0 = (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))))) \/ (~ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT1 0))))))).
Definition term186 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term131 := ~ (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT1 0))))).
Definition term256 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term154 (x0 : int) := real_sub (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term70 (x0 : int) := (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)))) \/ (int_le (int_add (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term145 := (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term111 (x0 : int) := real_add (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term168 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term149 (x0 : int) := ~ (~ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) \/ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))).
Definition term113 (x0 : int) := real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term143 := or (~ (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))).
Definition term189 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term16 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, forall y3 : int, ((y1 = (int_add (int_mul y0 y2) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y2)))) -> ((div y1 y2) = y0) /\ ((rem y1 y2) = y3)) x0.
Definition term1 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3)) x0.
Definition term77 (x0 : int) := real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term236 := (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term126 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term215 (x0 : int) := real_ge (real_sub (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term184 (x0 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term261 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term252 := ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))))).
Definition term238 := ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term198 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term193 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term158 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term6 (x0 : int) (x1 : int) (x2 : int) := forall y0 : int, ((x1 = (int_add (int_mul x0 x2) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x2)))) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = y0).
Definition term152 (x0 : int) := real_sub (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term26 := (forall y0 : int, (fun y1 : int => (div y1 (int_of_num (NUMERAL (BIT1 0)))) = y1) y0) /\ (forall y0 : int, (fun y1 : int => (rem y1 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0))) y0).
Definition term210 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1))) x1.
Definition term95 (x0 : int) := real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term112 (x0 : int) := real_le (real_of_int (int_add (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT1 0))))).
Definition term29 := fun y0 : int => (rem y0 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0)).
Definition term178 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term116 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term164 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term147 (x0 : int) := ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) \/ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term119 := int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)).
Definition term253 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term233 := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_abs (real_of_num (NUMERAL (BIT1 0))))).
Definition term38 (x0 : int) := rem x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term225 := real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term182 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term196 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term78 (x0 : int) := real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term255 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term36 := and (forall y0 : int, (div y0 (int_of_num (NUMERAL (BIT1 0)))) = y0).
Definition term140 := real_le (real_of_int (int_abs (int_of_num (NUMERAL (BIT1 0))))).
Definition term267 (x0 : int) := ~ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) \/ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term135 (x0 : int) := real_of_int (int_abs x0).
Definition term259 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term155 (x0 : int) := real_sub (real_of_int x0) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term199 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term192 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term127 := real_le (real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term133 := int_abs (int_of_num (NUMERAL (BIT1 0))).
Definition term109 (x0 : int) := real_add (real_of_int (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)))).
Definition term151 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term266 (x0 : int) := ((~ (~ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) \/ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))))) -> False) -> ~ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) \/ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term254 := real_le (real_of_num (NUMERAL 0)).
Definition term118 := ~ (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))).
Definition term75 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term262 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term33 := forall y0 : int, (fun y1 : int => (div y1 (int_of_num (NUMERAL (BIT1 0)))) = y1) y0.
Definition term93 (x0 : int) := real_mul (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term248 := and (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term106 (x0 : int) := int_add (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT1 0))).
Definition term31 (x0 : int) := div x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term35 := and (forall y0 : int, (fun y1 : int => (div y1 (int_of_num (NUMERAL (BIT1 0)))) = y1) y0).
Definition term83 (x0 : int) := real_add (real_of_int x0).
Definition term47 (x0 : int) := and ((div x0 (int_of_num (NUMERAL (BIT1 0)))) = x0).
Definition term241 := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term55 (x0 : int) := ~ (~ ((x0 = (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT1 0)))))))).
Definition term102 (x0 : int) := or (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)))).
Definition term144 := or (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term264 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term46 (x0 : int) := and ((fun y0 : int => (div y0 (int_of_num (NUMERAL (BIT1 0)))) = y0) x0).
Definition term188 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term79 (x0 : nat) := real_of_int (int_of_num x0).
Definition term207 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term237 := or ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term203 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term175 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term117 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term61 (x0 : int) := or (~ (x0 = (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))))).
Definition term76 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term190 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term122 := real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term263 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term179 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term224 := real_sub (real_of_num (NUMERAL 0)).
Definition term195 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term48 (x0 : int) := ((fun y0 : int => (div y0 (int_of_num (NUMERAL (BIT1 0)))) = y0) x0) /\ ((fun y0 : int => (rem y0 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0))) x0).
Definition term247 := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term244 := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term72 (x0 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))).
Definition term246 := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term231 := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL (BIT1 0))))).
Definition term250 := (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))).
Definition term229 := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_abs (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term27 := forall y0 : int, ((fun y1 : int => (div y1 (int_of_num (NUMERAL (BIT1 0)))) = y1) y0) /\ ((fun y1 : int => (rem y1 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0))) y0).
Definition term134 := real_le (real_of_int (int_abs (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num (NUMERAL 0))).
Definition term56 (x0 : int) := (x0 = (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT1 0)))))).
Definition term213 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term86 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term42 := forall y0 : int, (rem y0 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0)).
Definition term176 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term58 := (~ (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))) \/ (~ (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT1 0)))))).
Definition term66 := (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT1 0))))).
Definition term150 (x0 : int) := real_ge (real_sub (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term138 := real_abs (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term57 := ~ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT1 0)))))).
Definition term104 (x0 : int) := int_le (int_add (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term234 := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL (BIT1 0))))).
Definition term141 := real_le (real_abs (real_of_num (NUMERAL (BIT1 0)))).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1)).
Definition term180 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term243 := real_ge (real_of_num (NUMERAL (BIT1 0))).
Definition term227 := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term245 := real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term34 := forall y0 : int, (div y0 (int_of_num (NUMERAL (BIT1 0)))) = y0.
Definition term14 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y1 = (int_add (int_mul y0 y2) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y2)))) -> ((div y1 y2) = y0) /\ ((rem y1 y2) = y3).
Definition term13 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((y0 = (int_add (int_mul x0 y1) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y1)))) -> ((div y0 y1) = x0) /\ ((rem y0 y1) = y2).
Definition term12 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((x1 = (int_add (int_mul x0 y0) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs y0)))) -> ((div x1 y0) = x0) /\ ((rem x1 y0) = y1).
Definition term4 (x0 : int) (x1 : int) := forall y0 : int, forall y1 : int, ((x0 = (int_add (int_mul y0 x1) y1)) /\ ((int_le (int_of_num (NUMERAL 0)) y1) /\ (int_lt y1 (int_abs x1)))) -> ((div x0 x1) = y0) /\ ((rem x0 x1) = y1).
Definition term2 (x0 : int) := forall y0 : int, forall y1 : int, forall y2 : int, ((x0 = (int_add (int_mul y1 y0) y2)) /\ ((int_le (int_of_num (NUMERAL 0)) y2) /\ (int_lt y2 (int_abs y0)))) -> ((div x0 y0) = y1) /\ ((rem x0 y0) = y2).
Definition term0 := forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3).
Definition term172 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term216 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term100 (x0 : int) := real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term220 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((forall y2 : a0, y0 y2) /\ (forall y2 : a0, y1 y2)) = (forall y2 : a0, (y0 y2) /\ (y1 y2))) x0.
Definition term258 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term74 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term235 := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term50 := fun y0 : int => ((fun y1 : int => (div y1 (int_of_num (NUMERAL (BIT1 0)))) = y1) y0) /\ ((fun y1 : int => (rem y1 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0))) y0).
Definition term197 := S (Nat.add 0 0).
Definition term165 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term63 (x0 : int) := (~ (x0 = (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))))) \/ ((~ (int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)))) \/ (~ (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT1 0))))))).
Definition term139 := real_abs (real_of_num (NUMERAL (BIT1 0))).
Definition term159 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term101 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term167 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term222 := (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term96 (x0 : int) := real_add (real_of_int (int_mul x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term228 := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term105 (x0 : int) := real_le (real_of_int (int_add (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term103 (x0 : int) := or (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term205 := real_mul (real_of_num (NUMERAL 0)).
Definition term110 (x0 : int) := real_add (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term223 := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term15 := (forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3)) -> forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y1 = (int_add (int_mul y0 y2) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y2)))) -> ((div y1 y2) = y0) /\ ((rem y1 y2) = y3).
Definition term249 := and (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term85 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term230 := real_sub (real_of_num (NUMERAL 0)) (real_abs (real_of_num (NUMERAL (BIT1 0)))).
Definition term53 (x0 : int) := ((x0 = (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT1 0))))))) -> ((div x0 (int_of_num (NUMERAL (BIT1 0)))) = x0) /\ ((rem x0 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0))).
Definition term153 (x0 : int) := real_sub (real_of_int x0).
Definition term170 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term7 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (fun y0 : int => ((x1 = (int_add (int_mul x0 x2) y0)) /\ ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_lt y0 (int_abs x2)))) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = y0)) x3.
Definition term209 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term128 := real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term67 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term161 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term49 (x0 : int) := ((div x0 (int_of_num (NUMERAL (BIT1 0)))) = x0) /\ ((rem x0 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0))).
Definition term25 (x0 : int -> Prop) (x1 : int -> Prop) := forall y0 : int, (x0 y0) /\ (x1 y0).
Definition term114 (x0 : int) := real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term177 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term89 (x0 : int) := int_mul x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term71 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term88 (x0 : int) := real_add (real_of_int (int_mul x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num (NUMERAL 0))).
Definition term240 (x0 : real) (x1 : real) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) /\ (real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) x1).
Definition term251 := (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ ((real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)))).
Definition term115 (x0 : int) := (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term8 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((x1 = (int_add (int_mul x0 x2) x3)) /\ ((int_le (int_of_num (NUMERAL 0)) x3) /\ (int_lt x3 (int_abs x2)))) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = x3).
Definition term142 := real_le (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term173 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term181 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term208 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term81 := real_of_num (NUMERAL (BIT1 0)).
Definition term24 (x0 : int -> Prop) (x1 : int -> Prop) := (forall y0 : int, x0 y0) /\ (forall y0 : int, x1 y0).
Definition term214 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term60 := int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT1 0)))).
Definition term226 := real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term37 (x0 : int) := (fun y0 : int => (rem y0 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0))) x0.
Definition term242 := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term52 := forall y0 : int, ((div y0 (int_of_num (NUMERAL (BIT1 0)))) = y0) /\ ((rem y0 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0))).
Definition term97 (x0 : int) := real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term92 (x0 : int) := real_of_int (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term64 (x0 : int) := ~ ((x0 = (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)))) /\ ((int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0))) /\ (int_lt (int_of_num (NUMERAL 0)) (int_abs (int_of_num (NUMERAL (BIT1 0))))))).
Definition term69 (x0 : int) := ~ (x0 = (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)))).
Definition term43 := (forall y0 : int, (div y0 (int_of_num (NUMERAL (BIT1 0)))) = y0) /\ (forall y0 : int, (rem y0 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0))).
Definition term183 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term11 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := (forall y0 : int, forall y1 : int, forall y2 : int, forall y3 : int, ((y0 = (int_add (int_mul y2 y1) y3)) /\ ((int_le (int_of_num (NUMERAL 0)) y3) /\ (int_lt y3 (int_abs y1)))) -> ((div y0 y1) = y2) /\ ((rem y0 y1) = y3)) -> ((div x1 x2) = x0) /\ ((rem x1 x2) = x3).
Definition term257 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term90 (x0 : int) (x1 : int) := real_of_int (int_mul x0 x1).
Definition term65 (x0 : int) := int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)).
Definition term80 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term171 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term232 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs (real_of_num (NUMERAL (BIT1 0)))).
Definition term40 := fun y0 : int => (fun y1 : int => (rem y1 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0))) y0.
Definition term10 (x0 : int) (x1 : int) (x2 : int) (x3 : int) := ((div x1 x2) = x0) /\ ((rem x1 x2) = x3).
Definition term30 (x0 : int) := (fun y0 : int => (div y0 (int_of_num (NUMERAL (BIT1 0)))) = y0) x0.
Definition term219 (x0 : int) := real_sub (real_of_int x0) (real_add (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term59 := int_le (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL 0)).
Definition term136 (x0 : int) := real_abs (real_of_int x0).
Definition term84 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term212 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term157 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term191 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term160 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term123 := real_add (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term217 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term137 := real_of_int (int_abs (int_of_num (NUMERAL (BIT1 0)))).
Definition term108 (x0 : int) := real_add (real_of_int (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term166 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term239 (x0 : real) (x1 : real) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x0)) x1.
Definition term94 (x0 : int) := real_mul (real_of_int x0).
Definition term107 (x0 : int) := real_of_int (int_add (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))) (int_of_num (NUMERAL (BIT1 0)))).
Definition term130 (x0 : int) (x1 : int) := ~ (int_lt x0 x1).
Definition term125 := real_add (real_of_num (NUMERAL 0)).
Definition term265 (x0 : int) := (~ (~ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))) \/ (real_le (real_add (real_add (real_mul (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) \/ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_abs (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))))) -> False.
Definition term41 := forall y0 : int, (fun y1 : int => (rem y1 (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (NUMERAL 0))) y0.
Definition term206 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term221 := or (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term54 := int_of_num (NUMERAL (BIT1 0)).
Definition term132 := int_le (int_abs (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)).
Definition term87 (x0 : int) := real_of_int (int_add (int_mul x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))).
Definition term82 := NUMERAL (BIT1 0).
Definition term169 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
