Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term534 (x0 : int) := (fun y0 : int => forall y1 : real, (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_inv (real_pow y1 (num_of_int y0))) (real_pow y1 (num_of_int (int_neg y0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_pow y1 (num_of_int y0)) (real_inv (real_pow y1 (num_of_int (int_neg y0)))))))) -> (forall y2 : real, (real_inv (real_inv y2)) = y2) -> False) x0.
Definition term190 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ (((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))))).
Definition term265 (x0 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))).
Definition term199 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))).
Definition term457 (x0 : int) := exists y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) /\ (forall y1 : real, (real_inv (real_inv y1)) = y1).
Definition term391 (x0 : real) (x1 : int) := imp (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))))))).
Definition term80 (x0 : int) := real_le (real_add (real_neg (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term366 (x0 : real) (x1 : int) (x2 : real) (x3 : real) := ((~ (int_le (int_of_num (NUMERAL 0)) x1)) -> (real_pow x0 (num_of_int (int_neg x1))) = x2) -> ((~ (~ (int_le (int_of_num (NUMERAL 0)) x1))) -> (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1))))) = x3) -> (@COND real (int_le (int_of_num (NUMERAL 0)) (int_neg x1)) (real_pow x0 (num_of_int (int_neg x1))) (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1)))))) = (@COND real (~ (int_le (int_of_num (NUMERAL 0)) x1)) x2 x3).
Definition term420 (x0 : real) (x1 : int) := @COND real True (real_pow x0 (num_of_int x1)).
Definition term247 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term84 (x0 : int) := (real_le (real_add (real_neg (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term260 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term204 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term410 (x0 : real) (x1 : int) := real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1)))).
Definition term72 (x0 : int) := real_le (real_of_int (int_add (int_neg x0) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num (NUMERAL 0))).
Definition term100 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term449 (x0 : real -> Prop) := ~ (all x0).
Definition term533 := (~ False) -> False.
Definition term111 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term369 (x0 : real) (x1 : int) (x2 : real) := ((~ (~ (int_le (int_of_num (NUMERAL 0)) x1))) -> (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1))))) = x2) -> (@COND real (int_le (int_of_num (NUMERAL 0)) (int_neg x1)) (real_pow x0 (num_of_int (int_neg x1))) (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1)))))) = (@COND real (~ (int_le (int_of_num (NUMERAL 0)) x1)) (real_pow x0 (num_of_int (int_neg x1))) x2).
Definition term328 (x0 : int) := (x0 = (int_of_num (NUMERAL 0))) \/ (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term51 := real_add (real_of_int (int_of_num (NUMERAL 0))).
Definition term433 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ True.
Definition term287 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term206 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term408 (x0 : real) (x1 : int) := real_inv (real_pow x0 (num_of_int (int_neg x1))).
Definition term476 (x0 : int) := exists y0 : real, ~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0)))))).
Definition term240 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term294 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term430 (x0 : int) := ((((int_le (int_of_num (NUMERAL 0)) x0) = False) -> (forall y0 : real, (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_inv (real_pow y0 (num_of_int x0))) (real_pow y0 (num_of_int (int_neg x0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_pow y0 (num_of_int x0)) (real_inv (real_pow y0 (num_of_int (int_neg x0)))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1)) = (forall y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1))) /\ (((int_le (int_of_num (NUMERAL 0)) x0) = True) -> (forall y0 : real, (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_inv (real_pow y0 (num_of_int x0))) (real_pow y0 (num_of_int (int_neg x0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_pow y0 (num_of_int x0)) (real_inv (real_pow y0 (num_of_int (int_neg x0)))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1)) = True)) -> (forall y0 : real, (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_inv (real_pow y0 (num_of_int x0))) (real_pow y0 (num_of_int (int_neg x0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_pow y0 (num_of_int x0)) (real_inv (real_pow y0 (num_of_int (int_neg x0)))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1)) = (((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ True) /\ ((int_le (int_of_num (NUMERAL 0)) x0) \/ (forall y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1)))).
Definition term128 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term241 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term368 (x0 : real) (x1 : int) (x2 : real) := ((~ (int_le (int_of_num (NUMERAL 0)) x1)) -> (real_pow x0 (num_of_int (int_neg x1))) = (real_pow x0 (num_of_int (int_neg x1)))) -> ((~ (~ (int_le (int_of_num (NUMERAL 0)) x1))) -> (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1))))) = x2) -> (@COND real (int_le (int_of_num (NUMERAL 0)) (int_neg x1)) (real_pow x0 (num_of_int (int_neg x1))) (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1)))))) = (@COND real (~ (int_le (int_of_num (NUMERAL 0)) x1)) (real_pow x0 (num_of_int (int_neg x1))) x2).
Definition term99 (x0 : nat) := real_neg (real_of_num x0).
Definition term122 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term279 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term41 := real_of_int (int_of_num (NUMERAL 0)).
Definition term89 (x0 : Prop) := ~ (~ x0).
Definition term42 := real_of_num (NUMERAL 0).
Definition term349 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> (x0 = (int_of_num (NUMERAL 0))) = False.
Definition term379 (x0 : real) (x1 : int) := @eq real (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1)))).
Definition term434 (x0 : int) := and ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ True).
Definition term196 (x0 : int) := or (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))))).
Definition term1 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) -> (int_le (int_of_num (NUMERAL 0)) (int_neg x0)) = (~ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term419 (x0 : real) (x1 : int) := @eq real (real_inv (real_pow x0 (num_of_int x1))).
Definition term172 (x0 : int) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term25 (x0 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)).
Definition term150 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term48 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term362 (x0 : real) (x1 : int) (x2 : Prop) (x3 : real) := forall y0 : real, ((int_le (int_of_num (NUMERAL 0)) (int_neg x1)) = x2) -> (x2 -> (real_pow x0 (num_of_int (int_neg x1))) = x3) -> ((~ x2) -> (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1))))) = y0) -> (@COND real (int_le (int_of_num (NUMERAL 0)) (int_neg x1)) (real_pow x0 (num_of_int (int_neg x1))) (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1)))))) = (@COND real x2 x3 y0).
Definition term485 (x0 : Prop) (x1 : real -> Prop) := x0 /\ (exists y0 : real, x1 y0).
Definition term402 (x0 : real) (x1 : int) := @COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))).
Definition term71 (x0 : int) := int_le (int_add (int_neg x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)).
Definition term23 := int_of_num (NUMERAL 0).
Definition term81 (x0 : int) := real_le (real_add (real_neg (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term66 (x0 : int) := and (real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_int x0))).
Definition term21 (x0 : int) (x1 : int) := (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term325 (x0 : int) := ((~ (~ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ (((real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_int x0))) /\ (real_le (real_of_num (NUMERAL 0)) (real_of_int x0))) \/ ((real_le (real_add (real_neg (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))))) -> False) -> ~ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ (((real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_int x0))) /\ (real_le (real_of_num (NUMERAL 0)) (real_of_int x0))) \/ ((real_le (real_add (real_neg (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))).
Definition term407 (x0 : real) (x1 : int) := @COND real False (real_pow x0 (num_of_int x1)).
Definition term293 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term239 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term302 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term243 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term125 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term521 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term425 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term167 (x0 : int) := real_sub (real_of_num (NUMERAL 0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term137 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term443 (x0 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x0) \/ (forall y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1))).
Definition term388 := (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term317 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term256 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term271 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term332 (x0 : real) (x1 : int) := real_zpow x0 (int_neg x1).
Definition term386 (x0 : real) (x1 : int) := (((~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))))))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))))))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))))))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term161 (x0 : int) := and (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term411 (x0 : real) (x1 : int) := ~ ((real_pow x0 (num_of_int (int_neg x1))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1)))))).
Definition term529 (x0 : real) (x1 : int) := ((real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))) = (real_pow x0 (num_of_int (int_neg x1)))) /\ ((real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1)))))).
Definition term227 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term490 (x0 : int) := fun y0 : real => (fun y1 : real => (~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) /\ (forall y2 : real, (real_inv (real_inv y2)) = y2)) y0.
Definition term146 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term105 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term484 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term322 := S (Nat.add (BIT1 0) 0).
Definition term381 (x0 : Prop) := (~ x0) -> False.
Definition term423 := fun y0 : real => True.
Definition term526 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term451 (x0 : int) := ~ (forall y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1)).
Definition term127 (x0 : int) := real_sub (real_of_int x0) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term232 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term8 (x0 : int) := or ((int_le (int_of_num (NUMERAL 0)) (int_neg x0)) /\ (~ (~ (int_le (int_of_num (NUMERAL 0)) x0)))).
Definition term30 (x0 : int) := real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term474 (x0 : int) := fun y0 : real => (fun y1 : real => ~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) y0.
Definition term532 (x0 : real) (x1 : int) := ((real_pow x0 (num_of_int (int_neg x1))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1)))))) -> False.
Definition term133 (x0 : int) := real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term377 (x0 : Prop) (x1 : real) (x2 : real) := @COND real (~ x0) x1 x2.
Definition term160 (x0 : int) := real_ge (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term463 (x0 : real -> Prop) (x1 : Prop) := exists y0 : real, (x0 y0) /\ x1.
Definition term135 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term53 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term535 (x0 : int) (x1 : real) := (fun y0 : real => (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_inv (real_pow y0 (num_of_int x0))) (real_pow y0 (num_of_int (int_neg x0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_pow y0 (num_of_int x0)) (real_inv (real_pow y0 (num_of_int (int_neg x0)))))))) -> (forall y1 : real, (real_inv (real_inv y1)) = y1) -> False) x1.
Definition term329 (x0 : real) := (fun y0 : real => (real_zpow y0 (int_of_num (NUMERAL 0))) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term197 (x0 : int) := or (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))))).
Definition term13 (x0 : int) := int_le (int_of_num (NUMERAL 0)) (int_neg x0).
Definition term352 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term261 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term389 := ~ (forall y0 : real, (real_inv (real_inv y0)) = y0).
Definition term291 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term289 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term237 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term236 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term454 (x0 : int) (x1 : real) := ~ ((fun y0 : real => (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1)) x1).
Definition term95 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term480 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) /\ ((exists y0 : real, ~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) /\ (forall y0 : real, (real_inv (real_inv y0)) = y0)).
Definition term393 (x0 : int) := fun y0 : real => (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_inv (real_pow y0 (num_of_int x0))) (real_pow y0 (num_of_int (int_neg x0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_pow y0 (num_of_int x0)) (real_inv (real_pow y0 (num_of_int (int_neg x0)))))))) -> (forall y1 : real, (real_inv (real_inv y1)) = y1) -> False.
Definition term515 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term143 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term437 := fun y0 : real => (real_inv (real_inv y0)) = y0.
Definition term403 (x0 : real) (x1 : int) := @COND real False (real_inv (real_pow x0 (num_of_int x1))).
Definition term65 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term57 (x0 : int) := (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term266 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term219 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term169 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term159 (x0 : int) := real_ge (real_of_int x0).
Definition term483 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term73 (x0 : int) := int_add (int_neg x0) (int_of_num (NUMERAL (BIT1 0))).
Definition term530 (x0 : real) (x1 : int) := (((real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))) = (real_pow x0 (num_of_int (int_neg x1)))) /\ ((real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))))) -> (real_pow x0 (num_of_int (int_neg x1))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))).
Definition term424 := forall y0 : real, True.
Definition term494 (x0 : int) (x1 : real) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) /\ ((fun y0 : real => (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) /\ (forall y1 : real, (real_inv (real_inv y1)) = y1)) x1).
Definition term426 (x0 : Prop) := forall y0 : real, x0.
Definition term121 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term503 (x0 : Prop) := (~ x0) -> x0.
Definition term306 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)))).
Definition term115 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term68 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term79 (x0 : int) := real_le (real_of_int (int_add (int_neg x0) (int_of_num (NUMERAL (BIT1 0))))).
Definition term311 := real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term101 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term333 (x0 : real) (x1 : int) := @eq real (real_zpow x0 (int_neg x1)).
Definition term517 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term139 (x0 : int) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term195 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))))).
Definition term193 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))))).
Definition term409 (x0 : real) (x1 : int) := @COND real False (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))).
Definition term316 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term254 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term519 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term119 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term158 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term14 (x0 : int) := ~ (int_le (int_of_num (NUMERAL 0)) x0).
Definition term513 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term207 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term491 (x0 : int) := exists y0 : real, (fun y1 : real => (~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) /\ (forall y2 : real, (real_inv (real_inv y2)) = y2)) y0.
Definition term468 (x0 : int) (x1 : real) := (fun y0 : real => ~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) x1.
Definition term31 (x0 : int) := real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term431 (x0 : int) := ((~ (int_le (int_of_num (NUMERAL 0)) x0)) \/ True) /\ ((int_le (int_of_num (NUMERAL 0)) x0) \/ (forall y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1))).
Definition term198 (x0 : int) := (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))))) \/ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))))).
Definition term147 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term537 := forall y0 : real, forall y1 : int, (real_zpow y0 (int_neg y1)) = (real_inv (real_zpow y0 y1)).
Definition term360 (x0 : real) (x1 : int) (x2 : Prop) := forall y0 : real, forall y1 : real, ((int_le (int_of_num (NUMERAL 0)) (int_neg x1)) = x2) -> (x2 -> (real_pow x0 (num_of_int (int_neg x1))) = y0) -> ((~ x2) -> (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1))))) = y1) -> (@COND real (int_le (int_of_num (NUMERAL 0)) (int_neg x1)) (real_pow x0 (num_of_int (int_neg x1))) (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1)))))) = (@COND real x2 y0 y1).
Definition term255 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term376 (x0 : real) (x1 : int) := @COND real (~ (int_le (int_of_num (NUMERAL 0)) x1)) (real_pow x0 (num_of_int (int_neg x1))) (real_inv (real_pow x0 (num_of_int x1))).
Definition term514 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term10 (x0 : int) := ((int_le (int_of_num (NUMERAL 0)) (int_neg x0)) /\ (~ (~ (int_le (int_of_num (NUMERAL 0)) x0)))) \/ ((~ (int_le (int_of_num (NUMERAL 0)) (int_neg x0))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term493 (x0 : int) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (exists y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) /\ (forall y1 : real, (real_inv (real_inv y1)) = y1))).
Definition term492 (x0 : int) := @eq Prop ((~ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (exists y0 : real, (fun y1 : real => (~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) /\ (forall y2 : real, (real_inv (real_inv y2)) = y2)) y0)).
Definition term75 (x0 : int) := real_add (real_of_int (int_neg x0)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term173 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term432 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) \/ (forall y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1)).
Definition term313 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term365 (x0 : real) (x1 : int) (x2 : real) (x3 : real) := ((int_le (int_of_num (NUMERAL 0)) (int_neg x1)) = (~ (int_le (int_of_num (NUMERAL 0)) x1))) -> ((~ (int_le (int_of_num (NUMERAL 0)) x1)) -> (real_pow x0 (num_of_int (int_neg x1))) = x2) -> ((~ (~ (int_le (int_of_num (NUMERAL 0)) x1))) -> (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1))))) = x3) -> (@COND real (int_le (int_of_num (NUMERAL 0)) (int_neg x1)) (real_pow x0 (num_of_int (int_neg x1))) (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1)))))) = (@COND real (~ (int_le (int_of_num (NUMERAL 0)) x1)) x2 x3).
Definition term413 (x0 : real) (x1 : int) := (~ ((real_pow x0 (num_of_int (int_neg x1))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))))) -> ~ (forall y0 : real, (real_inv (real_inv y0)) = y0).
Definition term392 (x0 : real) (x1 : int) := (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))))))) -> ~ (forall y0 : real, (real_inv (real_inv y0)) = y0).
Definition term145 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term320 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term259 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term486 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 /\ (x1 y0).
Definition term2 (x0 : int) := ~ (~ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term441 := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) \/ (forall y1 : real, (~ ((real_pow y1 (num_of_int (int_neg y0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg y0))))))) -> ~ (forall y2 : real, (real_inv (real_inv y2)) = y2)).
Definition term292 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term238 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term235 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term132 (x0 : int) := real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term54 := real_le (real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term465 (x0 : int) := exists y0 : real, ((fun y1 : real => ~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) y0) /\ (forall y1 : real, (real_inv (real_inv y1)) = y1).
Definition term397 := fun y0 : int => forall y1 : real, (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_inv (real_pow y1 (num_of_int y0))) (real_pow y1 (num_of_int (int_neg y0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_pow y1 (num_of_int y0)) (real_inv (real_pow y1 (num_of_int (int_neg y0)))))))) -> (forall y2 : real, (real_inv (real_inv y2)) = y2) -> False.
Definition term383 (x0 : real) (x1 : int) := ~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1))))))).
Definition term511 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term9 (x0 : int) := or ((int_le (int_of_num (NUMERAL 0)) (int_neg x0)) /\ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term416 (x0 : int) := ((int_le (int_of_num (NUMERAL 0)) x0) = False) -> (forall y0 : real, (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_inv (real_pow y0 (num_of_int x0))) (real_pow y0 (num_of_int (int_neg x0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_pow y0 (num_of_int x0)) (real_inv (real_pow y0 (num_of_int (int_neg x0)))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1)) = (forall y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1)).
Definition term157 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term187 (x0 : int) := or ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))).
Definition term298 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term390 := forall y0 : real, (real_inv (real_inv y0)) = y0.
Definition term428 (x0 : int) := (((int_le (int_of_num (NUMERAL 0)) x0) = False) -> (forall y0 : real, (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_inv (real_pow y0 (num_of_int x0))) (real_pow y0 (num_of_int (int_neg x0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_pow y0 (num_of_int x0)) (real_inv (real_pow y0 (num_of_int (int_neg x0)))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1)) = (forall y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1))) /\ (((int_le (int_of_num (NUMERAL 0)) x0) = True) -> (forall y0 : real, (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_inv (real_pow y0 (num_of_int x0))) (real_pow y0 (num_of_int (int_neg x0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_pow y0 (num_of_int x0)) (real_inv (real_pow y0 (num_of_int (int_neg x0)))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1)) = True).
Definition term151 (x0 : int) := real_ge (real_sub (real_neg (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term60 := real_le (real_of_num (NUMERAL 0)).
Definition term28 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term262 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term501 (x0 : real) (x1 : int) := (~ ((real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))) = (real_pow x0 (num_of_int (int_neg x1))))) -> (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))) = (real_pow x0 (num_of_int (int_neg x1))).
Definition term46 (x0 : int) := int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term7 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) (int_neg x0)) /\ (int_le (int_of_num (NUMERAL 0)) x0).
Definition term11 (x0 : int) := ((int_le (int_of_num (NUMERAL 0)) (int_neg x0)) /\ (int_le (int_of_num (NUMERAL 0)) x0)) \/ ((~ (int_le (int_of_num (NUMERAL 0)) (int_neg x0))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term498 (x0 : int) := exists y0 : real, (~ (int_le (int_of_num (NUMERAL 0)) x0)) /\ ((~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) /\ (forall y1 : real, (real_inv (real_inv y1)) = y1)).
Definition term185 (x0 : int) := and (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term452 (x0 : int) := exists y0 : real, ~ ((fun y1 : real => (~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) -> ~ (forall y2 : real, (real_inv (real_inv y2)) = y2)) y0).
Definition term348 (x0 : real) (x1 : int) := @COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))).
Definition term310 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term134 (x0 : int) := or (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term92 (x0 : int) := real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term269 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term202 := real_lt (real_of_num (NUMERAL 0)).
Definition term37 (x0 : int) := real_add (real_of_int x0).
Definition term357 (x0 : real) (x1 : int) := real_pow x0 (num_of_int (int_neg x1)).
Definition term282 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term276 (x0 : int) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term186 (x0 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term90 (x0 : int) := ~ (~ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ (((real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_int x0))) /\ (real_le (real_of_num (NUMERAL 0)) (real_of_int x0))) \/ ((real_le (real_add (real_neg (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))))).
Definition term439 (x0 : int) := @eq Prop (forall y0 : real, (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_inv (real_pow y0 (num_of_int x0))) (real_pow y0 (num_of_int (int_neg x0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_pow y0 (num_of_int x0)) (real_inv (real_pow y0 (num_of_int (int_neg x0)))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1)).
Definition term67 (x0 : int) := (real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_int x0))) /\ (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term284 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term278 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term500 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term45 (x0 : int) := or (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term264 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term488 (x0 : int) := exists y0 : real, (~ (int_le (int_of_num (NUMERAL 0)) x0)) /\ ((fun y1 : real => (~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) /\ (forall y2 : real, (real_inv (real_inv y2)) = y2)) y0).
Definition term405 (x0 : real) (x1 : int) := @eq real (real_pow x0 (num_of_int (int_neg x1))).
Definition term6 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) (int_neg x0)) /\ (~ (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term295 := real_neg (real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term231 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term33 (x0 : nat) := real_of_int (int_of_num x0).
Definition term212 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term531 (x0 : real) (x1 : int) := (~ ((real_pow x0 (num_of_int (int_neg x1))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))))) -> (real_pow x0 (num_of_int (int_neg x1))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))).
Definition term242 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term112 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term466 (x0 : int) := (exists y0 : real, (fun y1 : real => ~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) y0) /\ (forall y0 : real, (real_inv (real_inv y0)) = y0).
Definition term175 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term69 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term344 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := @COND a0 (~ x0) x1 x2.
Definition term384 (x0 : real) (x1 : int) := (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))))))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term29 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term26 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num (NUMERAL 0))).
Definition term233 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term508 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term49 := real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term536 (x0 : real) := forall y0 : int, (real_zpow x0 (int_neg y0)) = (real_inv (real_zpow x0 y0)).
Definition term144 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term17 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (((int_le (int_of_num (NUMERAL 0)) (int_neg x0)) /\ (int_le (int_of_num (NUMERAL 0)) x0)) \/ ((~ (int_le (int_of_num (NUMERAL 0)) (int_neg x0))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)))).
Definition term191 (x0 : int) := (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))))) \/ (((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))))).
Definition term321 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term263 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term116 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term338 (x0 : int) := int_neg (int_neg x0).
Definition term165 := real_sub (real_of_num (NUMERAL 0)).
Definition term201 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term123 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term401 (x0 : int) := @COND real (int_le (int_of_num (NUMERAL 0)) x0).
Definition term138 (x0 : int) := real_sub (real_neg (real_of_int x0)).
Definition term308 := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)).
Definition term380 (x0 : real) (x1 : int) := real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1))))).
Definition term507 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term87 (x0 : int) := and ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term182 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term230 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0).
Definition term341 (a0 : Type') (x0 : Prop) (x1 : a0) := (fun y0 : a0 => forall y1 : a0, (@COND a0 (~ x0) y0 y1) = (@COND a0 x0 y1 y0)) x1.
Definition term436 (x0 : real) := real_inv (real_inv x0).
Definition term467 (x0 : int) := fun y0 : real => ~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0)))))).
Definition term518 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term83 (x0 : int) := and (real_le (real_add (real_neg (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term12 (x0 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) (int_neg x0)) = (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term347 (x0 : real) (x1 : int) := (fun y0 : int => (real_zpow x0 y0) = (@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_pow x0 (num_of_int y0)) (real_inv (real_pow x0 (num_of_int (int_neg y0)))))) x1.
Definition term85 (x0 : int) := or ((real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_int x0))) /\ (real_le (real_of_num (NUMERAL 0)) (real_of_int x0))).
Definition term290 := real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term40 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term363 (x0 : real) (x1 : int) (x2 : Prop) (x3 : real) (x4 : real) := (fun y0 : real => ((int_le (int_of_num (NUMERAL 0)) (int_neg x1)) = x2) -> (x2 -> (real_pow x0 (num_of_int (int_neg x1))) = x3) -> ((~ x2) -> (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1))))) = y0) -> (@COND real (int_le (int_of_num (NUMERAL 0)) (int_neg x1)) (real_pow x0 (num_of_int (int_neg x1))) (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1)))))) = (@COND real x2 x3 y0)) x4.
Definition term88 (x0 : int) := ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ (((real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_int x0))) /\ (real_le (real_of_num (NUMERAL 0)) (real_of_int x0))) \/ ((real_le (real_add (real_neg (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term461 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term335 (x0 : real) (x1 : int) := real_inv (real_zpow x0 x1).
Definition term113 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term44 (x0 : int) := or (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))).
Definition term499 (x0 : real) := (fun y0 : real => (real_inv (real_inv y0)) = y0) x0.
Definition term217 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term153 (x0 : int) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term497 (x0 : int) := fun y0 : real => (~ (int_le (int_of_num (NUMERAL 0)) x0)) /\ ((~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) /\ (forall y1 : real, (real_inv (real_inv y1)) = y1)).
Definition term58 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_neg x0)).
Definition term228 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term179 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term178 := real_div (real_of_num (NUMERAL (BIT1 0))).
Definition term225 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term215 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term342 (a0 : Type') (x0 : Prop) (x1 : a0) := forall y0 : a0, (@COND a0 (~ x0) x1 y0) = (@COND a0 x0 y0 x1).
Definition term56 (x0 : int) := real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term473 (x0 : int) := @eq Prop (exists y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) /\ (forall y1 : real, (real_inv (real_inv y1)) = y1)).
Definition term472 (x0 : int) := @eq Prop (exists y0 : real, ((fun y1 : real => ~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) y0) /\ (forall y1 : real, (real_inv (real_inv y1)) = y1)).
Definition term414 (x0 : int) := fun y0 : real => (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1).
Definition term394 (x0 : int) := fun y0 : real => (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_inv (real_pow y0 (num_of_int x0))) (real_pow y0 (num_of_int (int_neg x0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_pow y0 (num_of_int x0)) (real_inv (real_pow y0 (num_of_int (int_neg x0)))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1).
Definition term337 (x0 : int) := (fun y0 : int => (int_neg (int_neg y0)) = y0) x0.
Definition term117 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term450 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term502 (x0 : real) (x1 : int) := ~ ((real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))) = (real_pow x0 (num_of_int (int_neg x1)))).
Definition term130 (x0 : int) := real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term374 (x0 : real) (x1 : int) := (~ (~ (int_le (int_of_num (NUMERAL 0)) x1))) -> (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1))))) = (real_inv (real_pow x0 (num_of_int x1))).
Definition term275 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term400 := forall y0 : int, forall y1 : real, (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_inv (real_pow y1 (num_of_int y0))) (real_pow y1 (num_of_int (int_neg y0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_pow y1 (num_of_int y0)) (real_inv (real_pow y1 (num_of_int (int_neg y0)))))))) -> ~ (forall y2 : real, (real_inv (real_inv y2)) = y2).
Definition term399 := forall y0 : int, forall y1 : real, (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_inv (real_pow y1 (num_of_int y0))) (real_pow y1 (num_of_int (int_neg y0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_pow y1 (num_of_int y0)) (real_inv (real_pow y1 (num_of_int (int_neg y0)))))))) -> (forall y2 : real, (real_inv (real_inv y2)) = y2) -> False.
Definition term109 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term314 := real_ge (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term252 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term273 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term131 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term446 (x0 : real) (x1 : int) := (~ ((real_pow x0 (num_of_int (int_neg x1))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))))) /\ (~ (~ (forall y0 : real, (real_inv (real_inv y0)) = y0))).
Definition term350 (x0 : real) (x1 : int) := @COND real (int_le (int_of_num (NUMERAL 0)) (int_neg x1)) (real_pow x0 (num_of_int (int_neg x1))) (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1))))).
Definition term307 := Nat.mul (BIT0 (BIT1 0)) (BIT1 0).
Definition term251 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)).
Definition term209 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term319 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term258 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term435 (x0 : int) := True /\ ((int_le (int_of_num (NUMERAL 0)) x0) \/ (forall y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1))).
Definition term27 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term309 := real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0))).
Definition term422 := False -> ~ (forall y0 : real, (real_inv (real_inv y0)) = y0).
Definition term224 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term162 (x0 : int) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term208 := S (Nat.add 0 0).
Definition term303 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term102 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term456 (x0 : int) := fun y0 : real => (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) /\ (forall y1 : real, (real_inv (real_inv y1)) = y1).
Definition term22 (x0 : int) := (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))) \/ (int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term445 (x0 : real) (x1 : int) := and (~ ((real_pow x0 (num_of_int (int_neg x1))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))))).
Definition term444 := ~ (~ (forall y0 : real, (real_inv (real_inv y0)) = y0)).
Definition term398 := fun y0 : int => forall y1 : real, (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_inv (real_pow y1 (num_of_int y0))) (real_pow y1 (num_of_int (int_neg y0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_pow y1 (num_of_int y0)) (real_inv (real_pow y1 (num_of_int (int_neg y0)))))))) -> ~ (forall y2 : real, (real_inv (real_inv y2)) = y2).
Definition term96 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term475 (x0 : int) := exists y0 : real, (fun y1 : real => ~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) y0.
Definition term301 := real_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term305 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term104 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term326 (x0 : int) := ~ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ (((real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_int x0))) /\ (real_le (real_of_num (NUMERAL 0)) (real_of_int x0))) \/ ((real_le (real_add (real_neg (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))).
Definition term525 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term218 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)).
Definition term505 (x0 : real) (x1 : int) := ~ ((real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1)))))).
Definition term331 := int_neg (int_of_num (NUMERAL 0)).
Definition term469 (x0 : int) (x1 : real) := and ((fun y0 : real => ~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) x1).
Definition term184 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_neg (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term214 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term512 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term510 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term274 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term470 (x0 : int) (x1 : real) := ((fun y0 : real => ~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) x1) /\ (forall y0 : real, (real_inv (real_inv y0)) = y0).
Definition term364 (x0 : real) (x1 : int) (x2 : Prop) (x3 : real) (x4 : real) := ((int_le (int_of_num (NUMERAL 0)) (int_neg x1)) = x2) -> (x2 -> (real_pow x0 (num_of_int (int_neg x1))) = x3) -> ((~ x2) -> (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1))))) = x4) -> (@COND real (int_le (int_of_num (NUMERAL 0)) (int_neg x1)) (real_pow x0 (num_of_int (int_neg x1))) (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1)))))) = (@COND real x2 x3 x4).
Definition term47 (x0 : int) := real_le (real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term373 (x0 : real) (x1 : int) := real_inv (real_pow x0 (num_of_int x1)).
Definition term70 (x0 : int) := ~ (int_le (int_of_num (NUMERAL 0)) (int_neg x0)).
Definition term244 := real_mul (real_of_num (NUMERAL 0)).
Definition term356 (x0 : real) (x1 : int) := forall y0 : Prop, forall y1 : real, forall y2 : real, ((int_le (int_of_num (NUMERAL 0)) (int_neg x1)) = y0) -> (y0 -> (real_pow x0 (num_of_int (int_neg x1))) = y1) -> ((~ y0) -> (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1))))) = y2) -> (@COND real (int_le (int_of_num (NUMERAL 0)) (int_neg x1)) (real_pow x0 (num_of_int (int_neg x1))) (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1)))))) = (@COND real y0 y1 y2).
Definition term355 (x0 : Prop) (x1 : real) (x2 : real) := forall y0 : Prop, forall y1 : real, forall y2 : real, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND real x0 x1 x2) = (@COND real y0 y1 y2).
Definition term354 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term142 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term323 (x0 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term281 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term523 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term299 := NUMERAL (BIT0 (BIT1 0)).
Definition term63 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_int x0)).
Definition term163 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_neg (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term91 (x0 : int) := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term19 (x0 : int) := ~ (x0 = (int_of_num (NUMERAL 0))).
Definition term39 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term174 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term404 (x0 : real) (x1 : int) := @COND real False (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1))).
Definition term177 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term479 (x0 : int) := (exists y0 : real, ~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) /\ (forall y0 : real, (real_inv (real_inv y0)) = y0).
Definition term126 (x0 : int) := real_sub (real_of_int x0).
Definition term107 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term460 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (exists y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) /\ (forall y1 : real, (real_inv (real_inv y1)) = y1)).
Definition term180 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term246 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term361 (x0 : real) (x1 : int) (x2 : Prop) (x3 : real) := (fun y0 : real => forall y1 : real, ((int_le (int_of_num (NUMERAL 0)) (int_neg x1)) = x2) -> (x2 -> (real_pow x0 (num_of_int (int_neg x1))) = y0) -> ((~ x2) -> (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1))))) = y1) -> (@COND real (int_le (int_of_num (NUMERAL 0)) (int_neg x1)) (real_pow x0 (num_of_int (int_neg x1))) (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1)))))) = (@COND real x2 y0 y1)) x3.
Definition term55 := real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term20 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term62 (x0 : int) := real_neg (real_of_int x0).
Definition term98 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term283 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term277 (x0 : int) := ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term272 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term267 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term220 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term166 (x0 : int) := real_sub (real_of_num (NUMERAL 0)) (real_add (real_neg (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term189 (x0 : int) := and ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term495 (x0 : real) (x1 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x1)) /\ ((~ ((real_pow x0 (num_of_int (int_neg x1))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))))) /\ (forall y0 : real, (real_inv (real_inv y0)) = y0)).
Definition term378 (x0 : real) (x1 : int) := @COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1))).
Definition term296 := Nat.add (BIT1 0) (BIT1 0).
Definition term464 (x0 : real -> Prop) (x1 : Prop) := (exists y0 : real, x0 y0) /\ x1.
Definition term343 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (@COND a0 (~ x0) x1 y0) = (@COND a0 x0 y0 x1)) x2.
Definition term171 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term136 (x0 : int) := real_ge (real_sub (real_neg (real_of_int x0)) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term429 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (((x2 = False) -> x0 = x3) /\ ((x2 = True) -> x0 = x1)) -> x0 = (((~ x2) \/ x1) /\ (x2 \/ x3)).
Definition term129 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term114 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term82 (x0 : int) := and (~ (int_le (int_of_num (NUMERAL 0)) (int_neg x0))).
Definition term395 (x0 : int) := forall y0 : real, (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_inv (real_pow y0 (num_of_int x0))) (real_pow y0 (num_of_int (int_neg x0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_pow y0 (num_of_int x0)) (real_inv (real_pow y0 (num_of_int (int_neg x0)))))))) -> (forall y1 : real, (real_inv (real_inv y1)) = y1) -> False.
Definition term155 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term24 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term358 (x0 : real) (x1 : int) := real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1)))).
Definition term406 (x0 : real) (x1 : int) := @COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)).
Definition term176 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term504 (x0 : real) (x1 : int) := (~ ((real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))))) -> (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))).
Definition term280 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term124 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term382 (x0 : real) (x1 : int) := (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))))))) -> False.
Definition term385 (x0 : real) (x1 : int) := ((~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))))))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))))))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term375 (x0 : real) (x1 : int) := ((~ (~ (int_le (int_of_num (NUMERAL 0)) x1))) -> (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1))))) = (real_inv (real_pow x0 (num_of_int x1)))) -> (@COND real (int_le (int_of_num (NUMERAL 0)) (int_neg x1)) (real_pow x0 (num_of_int (int_neg x1))) (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1)))))) = (@COND real (~ (int_le (int_of_num (NUMERAL 0)) x1)) (real_pow x0 (num_of_int (int_neg x1))) (real_inv (real_pow x0 (num_of_int x1)))).
Definition term496 (x0 : int) := fun y0 : real => (~ (int_le (int_of_num (NUMERAL 0)) x0)) /\ ((fun y1 : real => (~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) /\ (forall y2 : real, (real_inv (real_inv y2)) = y2)) y0).
Definition term43 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term148 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term226 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term216 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term141 (x0 : int) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term458 (x0 : int) := and (~ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term156 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term353 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term340 (a0 : Type') (x0 : Prop) := forall y0 : a0, forall y1 : a0, (@COND a0 (~ x0) y0 y1) = (@COND a0 x0 y1 y0).
Definition term5 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) (int_neg x0)).
Definition term286 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term110 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term77 (x0 : int) := real_add (real_neg (real_of_int x0)).
Definition term118 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term421 (x0 : real) (x1 : int) := @COND real True (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))).
Definition term412 (x0 : real) (x1 : int) := imp (~ ((real_pow x0 (num_of_int (int_neg x1))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))))).
Definition term346 (x0 : real) := forall y0 : int, (real_zpow x0 y0) = (@COND real (int_le (int_of_num (NUMERAL 0)) y0) (real_pow x0 (num_of_int y0)) (real_inv (real_pow x0 (num_of_int (int_neg y0))))).
Definition term78 (x0 : int) := real_add (real_neg (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term528 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term520 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term211 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term35 := real_of_num (NUMERAL (BIT1 0)).
Definition term210 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term152 (x0 : int) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term516 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term297 := BIT0 (BIT1 0).
Definition term64 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term336 := real_inv (real_of_num (NUMERAL (BIT1 0))).
Definition term447 (x0 : real) (x1 : int) := (~ ((real_pow x0 (num_of_int (int_neg x1))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))))) /\ (forall y0 : real, (real_inv (real_inv y0)) = y0).
Definition term345 (x0 : real) := (fun y0 : real => forall y1 : int, (real_zpow y0 y1) = (@COND real (int_le (int_of_num (NUMERAL 0)) y1) (real_pow y0 (num_of_int y1)) (real_inv (real_pow y0 (num_of_int (int_neg y1)))))) x0.
Definition term477 (x0 : int) := and (exists y0 : real, (fun y1 : real => ~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) y0).
Definition term312 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term250 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term448 (x0 : real) (x1 : int) := ~ ((~ ((real_pow x0 (num_of_int (int_neg x1))) = (real_inv (real_inv (real_pow x0 (num_of_int (int_neg x1))))))) -> ~ (forall y0 : real, (real_inv (real_inv y0)) = y0)).
Definition term372 (x0 : real) (x1 : int) := real_pow x0 (num_of_int x1).
Definition term524 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term223 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term222 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term164 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term478 (x0 : int) := and (exists y0 : real, ~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))).
Definition term4 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) (int_neg x0))) /\ (~ (int_le (int_of_num (NUMERAL 0)) x0)).
Definition term120 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term455 (x0 : int) := fun y0 : real => ~ ((fun y1 : real => (~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) -> ~ (forall y2 : real, (real_inv (real_inv y2)) = y2)) y0).
Definition term318 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term257 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term205 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term415 (x0 : int) := forall y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1).
Definition term396 (x0 : int) := forall y0 : real, (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_inv (real_pow y0 (num_of_int x0))) (real_pow y0 (num_of_int (int_neg x0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_pow y0 (num_of_int x0)) (real_inv (real_pow y0 (num_of_int (int_neg x0)))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1).
Definition term188 (x0 : int) := ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term370 (x0 : int) := num_of_int (int_neg (int_neg x0)).
Definition term18 (x0 : int) := ~ ((~ (x0 = (int_of_num (NUMERAL 0)))) -> (int_le (int_of_num (NUMERAL 0)) (int_neg x0)) = (~ (int_le (int_of_num (NUMERAL 0)) x0))).
Definition term229 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term300 := real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term61 (x0 : int) := real_of_int (int_neg x0).
Definition term359 (x0 : real) (x1 : int) (x2 : Prop) := (fun y0 : Prop => forall y1 : real, forall y2 : real, ((int_le (int_of_num (NUMERAL 0)) (int_neg x1)) = y0) -> (y0 -> (real_pow x0 (num_of_int (int_neg x1))) = y1) -> ((~ y0) -> (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1))))) = y2) -> (@COND real (int_le (int_of_num (NUMERAL 0)) (int_neg x1)) (real_pow x0 (num_of_int (int_neg x1))) (real_inv (real_pow x0 (num_of_int (int_neg (int_neg x1)))))) = (@COND real y0 y1 y2)) x2.
Definition term181 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0).
Definition term270 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term34 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term183 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term334 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term527 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term108 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term339 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0, forall y2 : a0, (@COND a0 (~ y0) y1 y2) = (@COND a0 y0 y2 y1)) x0.
Definition term440 := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) \/ (forall y1 : real, (~ ((real_pow y1 (num_of_int (int_neg y0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg y0))))))) -> ~ (forall y2 : real, (real_inv (real_inv y2)) = y2)).
Definition term487 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (exists y0 : real, (fun y1 : real => (~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) /\ (forall y2 : real, (real_inv (real_inv y2)) = y2)) y0).
Definition term482 (x0 : int) := @eq Prop ((exists y0 : real, ~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) /\ (forall y0 : real, (real_inv (real_inv y0)) = y0)).
Definition term481 (x0 : int) := @eq Prop ((exists y0 : real, (fun y1 : real => ~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) y0) /\ (forall y0 : real, (real_inv (real_inv y0)) = y0)).
Definition term327 (x0 : int) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (int_of_num (NUMERAL 0))).
Definition term3 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term330 (x0 : real) := real_zpow x0 (int_of_num (NUMERAL 0)).
Definition term367 (x0 : real) (x1 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x1)) -> (real_pow x0 (num_of_int (int_neg x1))) = (real_pow x0 (num_of_int (int_neg x1))).
Definition term38 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term462 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term453 (x0 : int) (x1 : real) := (fun y0 : real => (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1)) x1.
Definition term442 (x0 : int) := (~ ((int_le (int_of_num (NUMERAL 0)) x0) \/ (forall y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1)))) -> False.
Definition term248 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term94 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term506 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term418 (x0 : real) (x1 : int) := @COND real True (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1))).
Definition term522 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term417 (x0 : real) (x1 : int) := @COND real True (real_inv (real_pow x0 (num_of_int x1))).
Definition term387 (x0 : real) (x1 : int) := (((~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))))))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))))))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> ((~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))))))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False) -> (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_inv (real_pow x0 (num_of_int x1))) (real_pow x0 (num_of_int (int_neg x1)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x1) (real_pow x0 (num_of_int x1)) (real_inv (real_pow x0 (num_of_int (int_neg x1)))))))) -> (forall y0 : real, (real_inv (real_inv y0)) = y0) -> False.
Definition term203 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term234 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term288 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term97 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term192 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term50 := real_add (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term59 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term315 := real_ge (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term253 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term509 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term103 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term149 := real_div (real_of_num (NUMERAL 0)).
Definition term459 (x0 : int) := (~ (int_le (int_of_num (NUMERAL 0)) x0)) /\ (~ (forall y0 : real, (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1))).
Definition term52 := real_add (real_of_num (NUMERAL 0)).
Definition term371 (x0 : real) (x1 : int) := real_pow x0 (num_of_int (int_neg (int_neg x1))).
Definition term74 (x0 : int) := real_of_int (int_add (int_neg x0) (int_of_num (NUMERAL (BIT1 0)))).
Definition term324 (x0 : int) := (~ (~ (((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) /\ (((real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_int x0))) /\ (real_le (real_of_num (NUMERAL 0)) (real_of_int x0))) \/ ((real_le (real_add (real_neg (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))))) -> False.
Definition term170 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term351 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term140 (x0 : int) := real_sub (real_neg (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term168 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term93 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term304 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term245 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term32 := int_of_num (NUMERAL (BIT1 0)).
Definition term438 (x0 : int) := or (int_le (int_of_num (NUMERAL 0)) x0).
Definition term249 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)).
Definition term86 (x0 : int) := ((real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_int x0))) /\ (real_le (real_of_num (NUMERAL 0)) (real_of_int x0))) \/ ((real_le (real_add (real_neg (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term36 := NUMERAL (BIT1 0).
Definition term15 (x0 : int) := and (~ (x0 = (int_of_num (NUMERAL 0)))).
Definition term16 (x0 : int) := (~ (x0 = (int_of_num (NUMERAL 0)))) /\ (~ ((int_le (int_of_num (NUMERAL 0)) (int_neg x0)) = (~ (int_le (int_of_num (NUMERAL 0)) x0)))).
Definition term200 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term471 (x0 : int) := fun y0 : real => ((fun y1 : real => ~ ((real_pow y1 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y1 (num_of_int (int_neg x0))))))) y0) /\ (forall y1 : real, (real_inv (real_inv y1)) = y1).
Definition term285 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term0 (x0 : int) := ~ (~ ((~ (x0 = (int_of_num (NUMERAL 0)))) -> (int_le (int_of_num (NUMERAL 0)) (int_neg x0)) = (~ (int_le (int_of_num (NUMERAL 0)) x0)))).
Definition term194 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))).
Definition term489 (x0 : int) (x1 : real) := (fun y0 : real => (~ ((real_pow y0 (num_of_int (int_neg x0))) = (real_inv (real_inv (real_pow y0 (num_of_int (int_neg x0))))))) /\ (forall y1 : real, (real_inv (real_inv y1)) = y1)) x1.
Definition term106 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term76 (x0 : int) := real_add (real_of_int (int_neg x0)).
Definition term268 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term221 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term213 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term154 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term427 (x0 : int) := ((int_le (int_of_num (NUMERAL 0)) x0) = True) -> (forall y0 : real, (~ ((@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_inv (real_pow y0 (num_of_int x0))) (real_pow y0 (num_of_int (int_neg x0)))) = (real_inv (@COND real (int_le (int_of_num (NUMERAL 0)) x0) (real_pow y0 (num_of_int x0)) (real_inv (real_pow y0 (num_of_int (int_neg x0)))))))) -> ~ (forall y1 : real, (real_inv (real_inv y1)) = y1)) = True.
