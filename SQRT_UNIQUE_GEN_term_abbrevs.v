Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term178 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term318 (x0 : real) := forall y0 : real, ((real_sub x0 y0) = (real_of_num (NUMERAL 0))) = (x0 = y0).
Definition term349 (x0 : real) (x1 : real) := and ((real_sgn x0) = (real_sgn x1)).
Definition term360 (x0 : real) (x1 : real) := ((real_sgn x0) = (real_sgn (sqrt x1))) /\ ((x0 = (sqrt x1)) \/ (x0 = (real_neg (sqrt x1)))).
Definition term218 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term111 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term135 (x0 : real) := @eq real (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term25 (x0 : real) := @eq real (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term267 (x0 : real) (x1 : real) := (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) /\ ((real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) = (real_of_num (NUMERAL 0))).
Definition term365 (x0 : real) (x1 : real) := (((real_sgn x1) = (real_sgn (sqrt x0))) /\ ((x1 = (sqrt x0)) \/ (x1 = (real_neg (sqrt x0))))) -> (sqrt x0) = x1.
Definition term95 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term371 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term224 (x0 : real) (x1 : real) := real_sub (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term230 (x0 : real) (x1 : real) := real_neg (real_sub (real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) (real_of_num (NUMERAL 0))).
Definition term183 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term262 (x0 : real) (x1 : real) := real_gt (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term263 (x0 : real) (x1 : real) := or (real_gt (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term249 (x0 : real) (x1 : real) := or (real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term356 (x0 : real) (x1 : real) := or ((real_sub x0 (sqrt x1)) = (real_of_num (NUMERAL 0))).
Definition term11 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term158 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term151 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) (real_of_num (NUMERAL 0)).
Definition term121 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term7 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term2 := real_of_num (NUMERAL 0).
Definition term51 (x0 : real) := real_neg (real_sub (real_neg x0) x0).
Definition term47 (x0 : real) := ((real_neg x0) = x0) /\ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term134 (x0 : real) := @eq real (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)).
Definition term213 (x0 : real) (x1 : real) := real_add (real_mul x0 x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term192 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_add x0 x1)) (real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x0 x1)).
Definition term261 (x0 : real) (x1 : real) := real_gt (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term293 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term191 (x0 : real) (x1 : real) := real_mul (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add x0 x1).
Definition term153 (x0 : real) := forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term205 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term206 (x0 : real) (x1 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term361 (x0 : real) (x1 : real) (x2 : Prop) := ((((real_sgn x0) = (real_sgn x1)) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x1))) = (((real_sgn x0) = (real_sgn (sqrt x1))) /\ ((x0 = (sqrt x1)) \/ (x0 = (real_neg (sqrt x1)))))) -> ((((real_sgn x0) = (real_sgn (sqrt x1))) /\ ((x0 = (sqrt x1)) \/ (x0 = (real_neg (sqrt x1))))) -> ((sqrt x1) = x0) = x2) -> ((((real_sgn x0) = (real_sgn x1)) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x1))) -> (sqrt x1) = x0) = ((((real_sgn x0) = (real_sgn (sqrt x1))) /\ ((x0 = (sqrt x1)) \/ (x0 = (real_neg (sqrt x1))))) -> x2).
Definition term340 (x0 : real) (x1 : real) (x2 : Prop) := ((((real_sgn x1) = (real_sgn (sqrt x1))) /\ ((real_abs x1) = (real_pow (sqrt x1) (NUMERAL (BIT0 (BIT1 0)))))) = (((real_sgn x1) = (real_sgn (sqrt x1))) /\ ((real_abs x1) = (real_pow (sqrt x1) (NUMERAL (BIT0 (BIT1 0))))))) -> ((((real_sgn x1) = (real_sgn (sqrt x1))) /\ ((real_abs x1) = (real_pow (sqrt x1) (NUMERAL (BIT0 (BIT1 0)))))) -> ((((real_sgn x0) = (real_sgn x1)) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x1))) -> (sqrt x1) = x0) = x2) -> ((((real_sgn x1) = (real_sgn (sqrt x1))) /\ ((real_abs x1) = (real_pow (sqrt x1) (NUMERAL (BIT0 (BIT1 0)))))) -> (((real_sgn x0) = (real_sgn x1)) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x1))) -> (sqrt x1) = x0) = ((((real_sgn x1) = (real_sgn (sqrt x1))) /\ ((real_abs x1) = (real_pow (sqrt x1) (NUMERAL (BIT0 (BIT1 0)))))) -> x2).
Definition term87 (x0 : real) := ((((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) \/ (((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))))).
Definition term212 (x0 : real) (x1 : real) := real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_add (real_mul x0 x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term252 (x0 : real) (x1 : real) := and ((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))).
Definition term391 (x0 : real) (x1 : Prop) := (((sqrt x0) = (real_of_num (NUMERAL 0))) -> ((sqrt x0) = (real_neg (sqrt x0))) = x1) -> (((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))) -> (sqrt x0) = (real_neg (sqrt x0))) = (((sqrt x0) = (real_of_num (NUMERAL 0))) -> x1).
Definition term284 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul y0 (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))) = (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term133 (x0 : real) := (fun y0 : real => (real_mul y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) = (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term280 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term43 (x0 : real) := or (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term238 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term298 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term312 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term92 := S (Nat.add (BIT1 0) 0).
Definition term357 (x0 : real) (x1 : real) := or (x0 = (sqrt x1)).
Definition term198 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_add x0 x1)).
Definition term372 (x0 : real) (x1 : real) := ((x1 = (sqrt x0)) \/ (x1 = (real_neg (sqrt x0)))) -> ((real_sgn x1) = (real_sgn (sqrt x0))) -> (sqrt x0) = x1.
Definition term335 (x0 : real) (x1 : real) := (((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1.
Definition term5 (x0 : real) := real_sub (real_neg x0).
Definition term67 (x0 : real) := real_gt (real_neg (real_sub (real_neg x0) x0)) (real_of_num (NUMERAL 0)).
Definition term315 (x0 : real) (x1 : real) := (~ (((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) = ((real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) = (real_of_num (NUMERAL 0))))) -> False.
Definition term162 (x0 : real) := (~ (((real_neg x0) = x0) = (x0 = (real_of_num (NUMERAL 0))))) -> False.
Definition term154 (x0 : real) := (fun y0 : real => (real_mul y0 x0) = (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term97 (x0 : real) := ((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) = (real_of_num (NUMERAL 0)).
Definition term176 (x0 : real) (x1 : real) := real_sub x0 (real_neg x1).
Definition term63 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0.
Definition term231 (x0 : real) (x1 : real) := real_neg (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term141 (x0 : nat) := real_add (real_of_num x0) (real_neg (real_of_num x0)).
Definition term393 := real_neg (real_of_num (NUMERAL 0)).
Definition term76 (x0 : real) := @eq real (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term203 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x0).
Definition term161 (x0 : real) := (fun y0 : real => (real_mul y0 x0) = (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term199 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul x0 x1)).
Definition term314 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))).
Definition term313 (x0 : real) (x1 : real) := (real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ ((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))).
Definition term216 (x0 : real) (x1 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1).
Definition term373 (x0 : real) := @eq real (real_sgn (sqrt x0)).
Definition term140 (x0 : real) := real_mul (real_add (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) x0.
Definition term9 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term91 := Peano.lt (NUMERAL 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term39 (x0 : real) := real_gt (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term381 (x0 : real) := real_neg (real_sgn (sqrt x0)).
Definition term352 (x0 : real) (x1 : real) := real_mul (real_sub x0 (sqrt x1)) (real_sub x0 (real_neg (sqrt x1))).
Definition term6 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term300 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term277 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term214 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term127 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)))).
Definition term32 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term40 (x0 : real) := real_gt (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term79 (x0 : real) := (~ ((real_neg x0) = x0)) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term190 (x0 : real) (x1 : real) := real_mul (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term220 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1))).
Definition term142 := real_add (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term257 (x0 : real) (x1 : real) := real_neg (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term147 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term269 (x0 : real) (x1 : real) := or (((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) /\ (~ ((real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) = (real_of_num (NUMERAL 0))))).
Definition term292 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term366 (x0 : real) (x1 : real) := (((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) -> ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = ((((real_sgn x1) = (real_sgn (sqrt x0))) /\ ((x1 = (sqrt x0)) \/ (x1 = (real_neg (sqrt x0))))) -> (sqrt x0) = x1).
Definition term143 := real_mul (real_add (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term30 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term398 := forall y0 : real, forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1.
Definition term179 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term53 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term233 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term299 (x0 : real) (x1 : real) := ((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term287 (x0 : real) (x1 : real) := ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term276 (x0 : real) (x1 : real) := ((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term181 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term57 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term65 (x0 : real) := real_gt (real_neg (real_sub (real_neg x0) x0)).
Definition term102 (x0 : real) := @eq real (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)).
Definition term28 (x0 : real) := real_sub x0 (real_of_num (NUMERAL 0)).
Definition term62 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term58 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))).
Definition term16 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term37 (x0 : real) := real_gt (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0)).
Definition term255 (x0 : real) (x1 : real) := ~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term136 (x0 : real) := ((real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))).
Definition term118 (x0 : real) := ((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term103 (x0 : real) := ((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term159 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term101 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term305 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul y0 (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))) = (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term99 (x0 : real) := (fun y0 : real => (real_mul y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) = (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term173 (x0 : real) (x1 : real) := @eq real (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term126 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term215 (x0 : real) (x1 : real) := real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)).
Definition term367 (x0 : real) (x1 : real) := ((((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) -> ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = ((((real_sgn x1) = (real_sgn (sqrt x0))) /\ ((x1 = (sqrt x0)) \/ (x1 = (real_neg (sqrt x0))))) -> (sqrt x0) = x1)) -> ((((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) -> (((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = ((((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) -> (((real_sgn x1) = (real_sgn (sqrt x0))) /\ ((x1 = (sqrt x0)) \/ (x1 = (real_neg (sqrt x0))))) -> (sqrt x0) = x1).
Definition term26 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term85 (x0 : real) := (((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) \/ (((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term222 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term241 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term29 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term364 (x0 : real) (x1 : real) := ((((real_sgn x1) = (real_sgn (sqrt x0))) /\ ((x1 = (sqrt x0)) \/ (x1 = (real_neg (sqrt x0))))) -> ((sqrt x0) = x1) = ((sqrt x0) = x1)) -> ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = ((((real_sgn x1) = (real_sgn (sqrt x0))) /\ ((x1 = (sqrt x0)) \/ (x1 = (real_neg (sqrt x0))))) -> (sqrt x0) = x1).
Definition term323 (x0 : real) (x1 : real) := (x0 = (real_of_num (NUMERAL 0))) \/ (x1 = (real_of_num (NUMERAL 0))).
Definition term388 (x0 : real) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))) = x1) -> (x1 -> ((sqrt x0) = (real_neg (sqrt x0))) = y0) -> (((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))) -> (sqrt x0) = (real_neg (sqrt x0))) = (x1 -> y0)) x2.
Definition term272 (x0 : real) (x1 : real) := ((real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ ((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0)))).
Definition term330 (x0 : real) := ((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0))))).
Definition term384 (x0 : real) := ((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))) -> (sqrt x0) = (real_neg (sqrt x0)).
Definition term325 (x0 : real) := ((real_sgn (sqrt x0)) = (real_sgn x0)) /\ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0)).
Definition term167 (x0 : real) (x1 : real) := (((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) /\ (~ ((real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) = (real_of_num (NUMERAL 0))))) \/ ((~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) /\ ((real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) = (real_of_num (NUMERAL 0)))).
Definition term291 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_add (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term290 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term253 (x0 : real) (x1 : real) := ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) /\ (~ ((real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) = (real_of_num (NUMERAL 0)))).
Definition term331 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term254 (x0 : real) (x1 : real) := ((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term42 (x0 : real) := or (real_gt (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term226 (x0 : real) (x1 : real) := real_sub (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term12 := real_neg (real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term200 (x0 : real) (x1 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x0 x1).
Definition term251 (x0 : real) (x1 : real) := and ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term109 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term184 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term78 (x0 : real) := and ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term237 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term168 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term52 (x0 : real) := real_neg (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term256 (x0 : real) (x1 : real) := (real_gt (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term175 (x0 : real) (x1 : real) := (real_gt (real_sub (real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0))).
Definition term27 (x0 : real) := (real_gt (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0))).
Definition term379 (x0 : real) := real_neg (real_sgn x0).
Definition term117 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term31 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term24 (x0 : real) := @eq real (real_sub (real_neg x0) x0).
Definition term34 (x0 : real) := @eq real (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))).
Definition term74 (x0 : real) := or (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))).
Definition term73 (x0 : real) := or (real_gt (real_sub (real_neg x0) x0) (real_of_num (NUMERAL 0))).
Definition term227 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term306 (x0 : real) (x1 : real) := @eq real (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term46 (x0 : real) := and ((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))).
Definition term392 := @eq real (real_of_num (NUMERAL 0)).
Definition term316 (x0 : real) (x1 : real) := ((~ (((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) = ((real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) = (real_of_num (NUMERAL 0))))) -> False) -> ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) = ((real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) = (real_of_num (NUMERAL 0))).
Definition term282 (x0 : real) (x1 : real) := ((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))) = (real_of_num (NUMERAL 0)).
Definition term376 (x0 : real) (x1 : real) := ((real_sgn x1) = (real_sgn (sqrt x0))) -> (sqrt x0) = x1.
Definition term129 := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)).
Definition term321 (x0 : real) := forall y0 : real, ((real_mul x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term41 (x0 : real) := real_gt x0 (real_of_num (NUMERAL 0)).
Definition term377 (x0 : real) := (fun y0 : real => (real_sgn (real_neg y0)) = (real_neg (real_sgn y0))) x0.
Definition term324 (x0 : real) := (fun y0 : real => ((real_sgn (sqrt y0)) = (real_sgn y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) x0.
Definition term395 (x0 : real) := (((sqrt x0) = (real_of_num (NUMERAL 0))) -> ((sqrt x0) = (real_neg (sqrt x0))) = True) -> (((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))) -> (sqrt x0) = (real_neg (sqrt x0))) = (((sqrt x0) = (real_of_num (NUMERAL 0))) -> True).
Definition term353 (x0 : real) (x1 : real) := ((real_sub x0 (sqrt x1)) = (real_of_num (NUMERAL 0))) \/ ((real_sub x0 (real_neg (sqrt x1))) = (real_of_num (NUMERAL 0))).
Definition term84 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term116 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term166 (x0 : real) (x1 : real) := ~ (((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) = ((real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) = (real_of_num (NUMERAL 0)))).
Definition term20 := real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term286 (x0 : real) (x1 : real) := @eq real (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term394 (x0 : real) := ((sqrt x0) = (real_of_num (NUMERAL 0))) -> ((sqrt x0) = (real_neg (sqrt x0))) = True.
Definition term302 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term279 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term169 (x0 : real) (x1 : real) := real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1)).
Definition term187 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term71 (x0 : real) := real_gt (real_sub (real_neg x0) x0) (real_of_num (NUMERAL 0)).
Definition term259 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term225 (x0 : real) (x1 : real) := real_sub (real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) (real_of_num (NUMERAL 0)).
Definition term209 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)).
Definition term346 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) = x2) -> (x2 -> ((sqrt x0) = x1) = y0) -> ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = (x2 -> y0)) x3.
Definition term338 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) = x2) -> (x2 -> ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = y0) -> ((((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) -> (((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = (x2 -> y0)) x3.
Definition term185 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term61 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term240 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) (real_of_num (NUMERAL 0)))).
Definition term303 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term266 (x0 : real) (x1 : real) := and ((real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term160 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)).
Definition term152 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)).
Definition term132 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term374 (x0 : real) (x1 : real) := imp ((real_sgn x0) = (real_sgn (sqrt x1))).
Definition term35 (x0 : real) := real_gt (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))).
Definition term319 (x0 : real) (x1 : real) := (fun y0 : real => ((real_sub x0 y0) = (real_of_num (NUMERAL 0))) = (x0 = y0)) x1.
Definition term210 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term83 (x0 : real) := (((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))) \/ (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term294 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term273 (x0 : real) (x1 : real) := (((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)))) \/ (((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term242 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0)).
Definition term21 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term320 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_mul y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) \/ (y1 = (real_of_num (NUMERAL 0))))) x0.
Definition term317 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_sub y0 y1) = (real_of_num (NUMERAL 0))) = (y0 = y1)) x0.
Definition term236 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term194 (x0 : real) (x1 : real) := real_add (real_mul x0 x0) (real_mul x0 x1).
Definition term89 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term128 := Nat.mul (BIT0 (BIT1 0)) (BIT1 0).
Definition term0 (x0 : real) := ~ (((real_neg x0) = x0) = (x0 = (real_of_num (NUMERAL 0)))).
Definition term202 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term50 (x0 : real) := (real_gt (real_sub (real_neg x0) x0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_neg x0) x0)) (real_of_num (NUMERAL 0))).
Definition term130 := real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0))).
Definition term148 := S (Nat.add 0 0).
Definition term382 (x0 : real) := @eq real (real_neg (real_sgn (sqrt x0))).
Definition term204 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term22 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term108 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0.
Definition term281 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term239 (x0 : real) (x1 : real) := @eq real (real_neg (real_sub (real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) (real_of_num (NUMERAL 0)))).
Definition term45 (x0 : real) := and ((real_neg x0) = x0).
Definition term10 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term397 (x0 : real) := forall y0 : real, (((real_sgn y0) = (real_sgn x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = y0.
Definition term81 (x0 : real) := or (((real_neg x0) = x0) /\ (~ (x0 = (real_of_num (NUMERAL 0))))).
Definition term359 (x0 : real) (x1 : real) := (x0 = (sqrt x1)) \/ (x0 = (real_neg (sqrt x1))).
Definition term90 := real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term19 := real_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term348 (x0 : real) := @eq real (real_sgn x0).
Definition term387 (x0 : real) (x1 : Prop) := forall y0 : Prop, (((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))) = x1) -> (x1 -> ((sqrt x0) = (real_neg (sqrt x0))) = y0) -> (((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))) -> (sqrt x0) = (real_neg (sqrt x0))) = (x1 -> y0).
Definition term345 (x0 : real) (x1 : real) (x2 : Prop) := forall y0 : Prop, ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) = x2) -> (x2 -> ((sqrt x0) = x1) = y0) -> ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = (x2 -> y0).
Definition term337 (x0 : real) (x1 : real) (x2 : Prop) := forall y0 : Prop, ((((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) = x2) -> (x2 -> ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = y0) -> ((((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) -> (((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = (x2 -> y0).
Definition term332 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term274 (x0 : real) (x1 : real) := or ((((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)))) \/ (((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))))).
Definition term86 (x0 : real) := or ((((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) \/ (((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term390 (x0 : real) (x1 : Prop) := (((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))) = ((sqrt x0) = (real_of_num (NUMERAL 0)))) -> (((sqrt x0) = (real_of_num (NUMERAL 0))) -> ((sqrt x0) = (real_neg (sqrt x0))) = x1) -> (((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))) -> (sqrt x0) = (real_neg (sqrt x0))) = (((sqrt x0) = (real_of_num (NUMERAL 0))) -> x1).
Definition term124 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_neg (real_of_num x1)).
Definition term327 (x0 : real) := and ((real_sgn (sqrt x0)) = (real_sgn x0)).
Definition term304 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term295 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term1 (x0 : real) := (((real_neg x0) = x0) /\ (~ (x0 = (real_of_num (NUMERAL 0))))) \/ ((~ ((real_neg x0) = x0)) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term195 (x0 : real) := real_add (real_mul x0 x0).
Definition term370 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term112 := real_mul (real_of_num (NUMERAL 0)).
Definition term385 (x0 : real) := forall y0 : Prop, forall y1 : Prop, (((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))) = y0) -> (y0 -> ((sqrt x0) = (real_neg (sqrt x0))) = y1) -> (((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))) -> (sqrt x0) = (real_neg (sqrt x0))) = (y0 -> y1).
Definition term342 (x0 : real) (x1 : real) := forall y0 : Prop, forall y1 : Prop, ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) = y0) -> (y0 -> ((sqrt x0) = x1) = y1) -> ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = (y0 -> y1).
Definition term334 (x0 : real) (x1 : real) := forall y0 : Prop, forall y1 : Prop, ((((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) = y0) -> (y0 -> ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = y1) -> ((((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) -> (((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = (y0 -> y1).
Definition term333 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term70 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term66 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term36 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term171 (x0 : real) (x1 : real) := real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term23 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0.
Definition term4 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term17 := NUMERAL (BIT0 (BIT1 0)).
Definition term296 (x0 : real) := real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term138 (x0 : real) := real_gt (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) (real_of_num (NUMERAL 0)).
Definition term106 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term44 (x0 : real) := (real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term341 (x0 : real) (x1 : real) (x2 : Prop) := ((((real_sgn x1) = (real_sgn (sqrt x1))) /\ ((real_abs x1) = (real_pow (sqrt x1) (NUMERAL (BIT0 (BIT1 0)))))) -> ((((real_sgn x0) = (real_sgn x1)) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x1))) -> (sqrt x1) = x0) = x2) -> ((((real_sgn x1) = (real_sgn (sqrt x1))) /\ ((real_abs x1) = (real_pow (sqrt x1) (NUMERAL (BIT0 (BIT1 0)))))) -> (((real_sgn x0) = (real_sgn x1)) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x1))) -> (sqrt x1) = x0) = ((((real_sgn x1) = (real_sgn (sqrt x1))) /\ ((real_abs x1) = (real_pow (sqrt x1) (NUMERAL (BIT0 (BIT1 0)))))) -> x2).
Definition term122 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term351 (x0 : real) := @eq real (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term186 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term207 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1).
Definition term170 (x0 : real) (x1 : real) := real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term14 := Nat.add (BIT1 0) (BIT1 0).
Definition term75 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term80 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term172 (x0 : real) (x1 : real) := @eq real (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term88 (x0 : real) := ((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term125 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term201 (x0 : real) (x1 : real) := real_add (real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x0) (real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1).
Definition term55 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term363 (x0 : real) (x1 : real) := (((real_sgn x1) = (real_sgn (sqrt x0))) /\ ((x1 = (sqrt x0)) \/ (x1 = (real_neg (sqrt x0))))) -> ((sqrt x0) = x1) = ((sqrt x0) = x1).
Definition term326 (x0 : real) := real_sgn (sqrt x0).
Definition term329 (x0 : real) := real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term110 := real_add (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term350 (x0 : real) (x1 : real) := and ((real_sgn x0) = (real_sgn (sqrt x1))).
Definition term328 (x0 : real) := and ((real_sgn x0) = (real_sgn (sqrt x0))).
Definition term355 (x0 : real) (x1 : real) := real_sub x0 (real_neg (sqrt x1)).
Definition term211 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul x0 x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term268 (x0 : real) (x1 : real) := ((real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))).
Definition term358 (x0 : real) := real_neg (sqrt x0).
Definition term347 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) = x2) -> (x2 -> ((sqrt x0) = x1) = x3) -> ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = (x2 -> x3).
Definition term339 (x0 : real) (x1 : real) (x2 : Prop) (x3 : Prop) := ((((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) = x2) -> (x2 -> ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = x3) -> ((((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) -> (((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = (x2 -> x3).
Definition term354 (x0 : real) (x1 : real) := real_sub x0 (sqrt x1).
Definition term378 (x0 : real) := real_sgn (real_neg x0).
Definition term182 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term270 (x0 : real) (x1 : real) := or (((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))))).
Definition term82 (x0 : real) := or (((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term193 (x0 : real) (x1 : real) := real_mul x0 (real_add x0 x1).
Definition term100 := real_of_num (NUMERAL (BIT1 0)).
Definition term15 := BIT0 (BIT1 0).
Definition term248 (x0 : real) (x1 : real) := or (real_gt (real_sub (real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term396 (x0 : real) := ((sqrt x0) = (real_of_num (NUMERAL 0))) -> True.
Definition term48 (x0 : real) := ((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term322 (x0 : real) (x1 : real) := (fun y0 : real => ((real_mul x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) \/ (y0 = (real_of_num (NUMERAL 0))))) x1.
Definition term174 (x0 : real) (x1 : real) := ~ ((real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) = (real_of_num (NUMERAL 0))).
Definition term33 (x0 : real) := real_neg (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term164 := forall y0 : real, ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0))).
Definition term113 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term131 := real_mul (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term180 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term123 (x0 : real) := real_mul (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term54 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) x0.
Definition term311 (x0 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term228 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term232 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term260 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term386 (x0 : real) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))) = y0) -> (y0 -> ((sqrt x0) = (real_neg (sqrt x0))) = y1) -> (((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))) -> (sqrt x0) = (real_neg (sqrt x0))) = (y0 -> y1)) x1.
Definition term60 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term283 (x0 : real) (x1 : real) := forall y0 : real, (real_mul y0 (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))) = (real_of_num (NUMERAL 0)).
Definition term98 (x0 : real) := forall y0 : real, (real_mul y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) = (real_of_num (NUMERAL 0)).
Definition term3 (x0 : real) := real_sub (real_neg x0) x0.
Definition term308 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term289 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term247 (x0 : real) (x1 : real) := real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term389 (x0 : real) (x1 : Prop) (x2 : Prop) := (((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))) = x1) -> (x1 -> ((sqrt x0) = (real_neg (sqrt x0))) = x2) -> (((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))) -> (sqrt x0) = (real_neg (sqrt x0))) = (x1 -> x2).
Definition term244 (x0 : real) (x1 : real) := real_gt (real_sub (real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) (real_of_num (NUMERAL 0))).
Definition term246 (x0 : real) (x1 : real) := real_gt (real_sub (real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term375 (x0 : real) := @eq real (sqrt x0).
Definition term139 (x0 : real) := real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0).
Definition term107 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0).
Definition term8 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term18 := real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term229 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term285 (x0 : real) (x1 : real) := @eq real (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term196 (x0 : real) := real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term219 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term155 (x0 : real) := (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term145 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term56 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term245 (x0 : real) (x1 : real) := real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term297 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term69 (x0 : real) := real_gt (real_sub (real_neg x0) x0).
Definition term96 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term49 (x0 : real) := ~ ((real_neg x0) = x0).
Definition term264 (x0 : real) (x1 : real) := @eq real (real_sub (real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))) (real_of_num (NUMERAL 0))).
Definition term72 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)).
Definition term68 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term38 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term343 (x0 : real) (x1 : real) := ((real_sgn x0) = (real_sgn x1)) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x1)).
Definition term189 (x0 : real) (x1 : real) := real_mul (real_sub x0 x1).
Definition term144 (x0 : real) := real_gt (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)).
Definition term114 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)).
Definition term188 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term235 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term362 (x0 : real) (x1 : real) (x2 : Prop) := ((((real_sgn x0) = (real_sgn (sqrt x1))) /\ ((x0 = (sqrt x1)) \/ (x0 = (real_neg (sqrt x1))))) -> ((sqrt x1) = x0) = x2) -> ((((real_sgn x0) = (real_sgn x1)) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x1))) -> (sqrt x1) = x0) = ((((real_sgn x0) = (real_sgn (sqrt x1))) /\ ((x0 = (sqrt x1)) \/ (x0 = (real_neg (sqrt x1))))) -> x2).
Definition term163 (x0 : real) := ((~ (((real_neg x0) = x0) = (x0 = (real_of_num (NUMERAL 0))))) -> False) -> ((real_neg x0) = x0) = (x0 = (real_of_num (NUMERAL 0))).
Definition term217 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term383 (x0 : real) := imp ((real_neg (real_sgn (sqrt x0))) = (real_sgn (sqrt x0))).
Definition term165 (x0 : real) := (fun y0 : real => ((real_sgn y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) x0.
Definition term307 (x0 : real) (x1 : real) := (((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term301 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term288 (x0 : real) (x1 : real) := (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term278 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term156 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term149 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0))).
Definition term119 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term234 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term275 (x0 : real) (x1 : real) := ((((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)))) \/ (((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))))) \/ (((real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ ((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))))).
Definition term344 (x0 : real) (x1 : real) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) = y0) -> (y0 -> ((sqrt x0) = x1) = y1) -> ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = (y0 -> y1)) x2.
Definition term336 (x0 : real) (x1 : real) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) = y0) -> (y0 -> ((((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = y1) -> ((((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) -> (((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1) = (y0 -> y1)) x2.
Definition term221 := real_add (real_of_num (NUMERAL 0)).
Definition term380 (x0 : real) := real_sgn (real_neg (sqrt x0)).
Definition term177 (x0 : real) (x1 : real) := real_sub x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term157 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term150 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) (real_of_num (NUMERAL 0)).
Definition term137 (x0 : real) := (((real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0)) (real_of_num (NUMERAL 0)).
Definition term120 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term105 (x0 : real) := (((real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) x0) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term271 (x0 : real) (x1 : real) := (((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0))) /\ ((real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))))) \/ (((real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) = (real_of_num (NUMERAL 0)))).
Definition term223 (x0 : real) (x1 : real) := real_sub (real_mul (real_sub x0 x1) (real_sub x0 (real_neg x1))).
Definition term59 := Nat.mul (BIT1 0) (BIT0 (BIT1 0)).
Definition term250 (x0 : real) (x1 : real) := (real_gt (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term208 (x0 : real) (x1 : real) := real_add (real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term64 (x0 : real) := @eq real (real_neg (real_sub (real_neg x0) x0)).
Definition term93 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term13 := NUMERAL (BIT1 0).
Definition term104 (x0 : real) (x1 : real) := ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term94 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term146 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term265 (x0 : real) (x1 : real) := and (~ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term369 (x0 : real) (x1 : real) := (((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) -> (((real_sgn x1) = (real_sgn (sqrt x0))) /\ ((x1 = (sqrt x0)) \/ (x1 = (real_neg (sqrt x0))))) -> (sqrt x0) = x1.
Definition term368 (x0 : real) (x1 : real) := (((real_sgn x0) = (real_sgn (sqrt x0))) /\ ((real_abs x0) = (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))))) -> (((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1.
Definition term197 (x0 : real) (x1 : real) := real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul x0 x1).
Definition term243 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term258 (x0 : real) (x1 : real) := @eq real (real_neg (real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term77 (x0 : real) := and (~ ((real_neg x0) = x0)).
Definition term115 := real_gt (real_of_num (NUMERAL 0)).
Definition term310 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term309 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
