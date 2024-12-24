Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (@SUBSET a0 x0 y0).
Definition term131 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := imp (@IN a0 x0 (@DIFF a0 x1 x2)).
Definition term241 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (x0 y0) -> x1 y0.
Definition term208 (x0 : int) (x1 : int) := int_le x0 (int_add x0 x1).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((x0 x2) /\ (~ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2)))))).
Definition term325 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term373 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term339 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term280 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term253 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term107 := (~ False) -> False.
Definition term186 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ ((y0 y2) /\ ((y1 y2) /\ (~ (y0 y2)))))) -> False) x0.
Definition term153 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2)) -> False) x0.
Definition term114 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ ((forall y2 : a0, (y0 y2) -> y1 y2) -> forall y2 : a0, (y1 y2) = ((y0 y2) \/ ((y1 y2) /\ (~ (y0 y2)))))) -> False) x0.
Definition term265 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (forall y0 : a0, (x0 y0) -> x1 y0).
Definition term302 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) \/ (@IN a0 x1 x2).
Definition term309 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> @FINITE a0 x0.
Definition term316 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term180 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ~ ((x0 y1) /\ ((y0 y1) /\ (~ (x0 y1)))).
Definition term317 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term334 (x0 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term252 (x0 : nat) := real_neg (real_of_num x0).
Definition term218 := real_of_int (int_of_num (NUMERAL 0)).
Definition term74 (x0 : Prop) := ~ (~ x0).
Definition term219 := real_of_num (NUMERAL 0).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) \/ (~ (x1 x2)).
Definition term277 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term80 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (forall y2 : a0, (y0 y2) -> y1 y2) -> forall y2 : a0, (y1 y2) = ((y0 y2) \/ ((y1 y2) /\ (~ (y0 y2)))).
Definition term199 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) (@CARD a0 x0).
Definition term216 := int_of_num (NUMERAL 0).
Definition term158 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @INTER a0 x1 (@DIFF a0 x0 x1).
Definition term379 (x0 : int) (x1 : int) := ((~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x1) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))))) -> False) -> ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x1) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))).
Definition term315 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term319 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term276 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (~ (x1 x2)).
Definition term239 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) /\ ((@FINITE a0 x1) /\ ((@INTER a0 x0 x1) = (@EMPTY a0))).
Definition term116 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @CARD a0 (@UNION a0 x1 (@DIFF a0 x0 x1)).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @UNION a0 x1 (@DIFF a0 x0 x1).
Definition term301 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term369 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term358 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term134 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) /\ (~ (x0 x2))) -> x1 x2.
Definition term203 (x0 : int) (x1 : int) := ~ (~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> int_le x0 (int_add x0 x1))).
Definition term184 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ~ ((y0 y2) /\ ((y1 y2) /\ (~ (y0 y2)))).
Definition term151 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2.
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x1 x2)) /\ (~ ((x0 x2) /\ (~ (x1 x2)))).
Definition term260 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (@IN a0 x0 x1).
Definition term289 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term67 (x0 : Prop) := (~ x0) -> False.
Definition term211 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (~ (int_le x0 (int_add x0 x1)))).
Definition term304 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x0 x2) = ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2)))))) -> False.
Definition term275 (x0 : int) := real_ge (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term136 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((x1 y0) /\ (~ (x0 y0))) -> x1 y0.
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := True /\ (@SUBSET a0 (@DIFF a0 x1 x0) x1).
Definition term159 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INTER a0 x1 (@DIFF a0 x0 x1))) = (@IN a0 y0 (@EMPTY a0)).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> @FINITE a0 x1.
Definition term374 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) /\ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2)))).
Definition term126 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0 -> Prop, (@FINITE a0 y0) /\ (@SUBSET a0 (@DIFF a0 x0 x1) y0)) -> @FINITE a0 (@DIFF a0 x0 x1).
Definition term313 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term308 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term286 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term111 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term251 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term222 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term350 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (x0 x1)).
Definition term22 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ ((@INTER a0 y0 y1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 y0 y1)) = (Nat.add (@CARD a0 y0) (@CARD a0 y1))) -> forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ ((@INTER a0 y0 y1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 y0 y1)) = (Nat.add (@CARD a0 y0) (@CARD a0 y1)).
Definition term274 (x0 : int) := real_ge (real_of_int x0).
Definition term242 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_of_int x1) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1).
Definition term59 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (@SUBSET a0 x0 x1).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term329 (x0 : int) := real_add (real_of_num (NUMERAL 0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term185 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) /\ ((x0 x2) /\ (~ (x1 x2)))) -> False.
Definition term105 (x0 : Prop) := (~ x0) -> x0.
Definition term293 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term223 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term118 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : nat => Peano.le (@CARD a0 x0) y0.
Definition term255 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term382 (a0 : Type') (x0 : a0 -> Prop) := int_of_num (@CARD a0 x0).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, (x1 y0) -> x0 y0) -> forall y0 : a0, (x0 y0) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, (@IN a0 y0 x1) -> @IN a0 y0 x0) -> forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 (@UNION a0 x1 (@DIFF a0 x0 x1))).
Definition term231 (x0 : int) (x1 : int) := real_of_int (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0)))).
Definition term166 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((x1 x2) /\ ((x0 x2) /\ (~ (x1 x2)))).
Definition term367 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term227 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add x1 x0) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x1).
Definition term298 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 x0) /\ ((@FINITE a0 y0) /\ ((@INTER a0 x0 y0) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 x0 y0)) = (Nat.add (@CARD a0 x0) (@CARD a0 y0)).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term296 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term273 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term311 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x0 x1) /\ (@FINITE a0 x1).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ ((@INTER a0 y0 y1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 y0 y1)) = (Nat.add (@CARD a0 y0) (@CARD a0 y1))) -> (@CARD a0 (@UNION a0 x0 x1)) = (Nat.add (@CARD a0 x0) (@CARD a0 x1)).
Definition term283 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term267 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term368 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term333 (x0 : int) := and (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term160 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@INTER a0 x1 x2).
Definition term55 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@DIFF a0 x1 x2).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (x0 x1).
Definition term259 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term372 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term314 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term307 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term272 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ ((@FINITE a0 x1) /\ ((@INTER a0 x0 x1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 x0 x1)) = (Nat.add (@CARD a0 x0) (@CARD a0 x1)).
Definition term127 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @SUBSET a0 (@DIFF a0 x1 x0) x1.
Definition term189 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ ((@FINITE a0 (@DIFF a0 x0 x1)) /\ ((@INTER a0 x1 (@DIFF a0 x0 x1)) = (@EMPTY a0))).
Definition term221 := real_le (real_of_num (NUMERAL 0)).
Definition term178 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ~ ((x0 y1) /\ ((y0 y1) /\ (~ (x0 y1)))).
Definition term229 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term375 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term49 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 x1 x2).
Definition term282 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term337 := real_lt (real_of_num (NUMERAL 0)).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (~ (x0 x2))) -> x1 x2.
Definition term235 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_int x1)).
Definition term271 (x0 : int) := real_add (real_of_int x0).
Definition term102 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x0 x2) /\ ((~ (x1 x2)) /\ ((~ (x0 x2)) \/ (x1 x2)))) \/ ((~ (x0 x2)) /\ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2))))).
Definition term300 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term125 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term246 (x0 : int) (x1 : int) := ~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x1) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))))).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((fun y0 : a0 -> Prop => Peano.le (@CARD a0 x0) (@CARD a0 y0)) x1).
Definition term377 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term385 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1)) -> Peano.le (@CARD a0 x0) (@CARD a0 x1).
Definition term386 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@SUBSET a0 x0 y0) /\ (@FINITE a0 y0)) -> Peano.le (@CARD a0 x0) (@CARD a0 y0).
Definition term303 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term217 (x0 : nat) := real_of_int (int_of_num x0).
Definition term322 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term57 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term318 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term266 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term224 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term230 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term305 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term200 (a0 : Type') (x0 : a0 -> Prop) := int_le (int_of_num (NUMERAL 0)) (int_of_num (@CARD a0 x0)).
Definition term258 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term196 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @CARD a0 (@DIFF a0 x0 x1).
Definition term152 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> False.
Definition term376 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term294 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Peano.le (@CARD a0 x1) (Nat.add (@CARD a0 x1) (@CARD a0 (@DIFF a0 x0 x1))).
Definition term173 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term140 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (forall y0 : a0, ((x1 y0) /\ (~ (x0 y0))) -> x1 y0)) -> False) -> (~ (forall y0 : a0, ((x1 y0) /\ (~ (x0 y0))) -> x1 y0)) -> False.
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ ((forall y0 : a0, (x1 y0) -> x0 y0) -> forall y0 : a0, (x0 y0) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ ((forall y0 : a0, (x1 y0) -> x0 y0) -> forall y0 : a0, (x0 y0) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term335 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))).
Definition term310 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term331 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (~ (~ (x0 x1))).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (@SUBSET a0 x0 x1).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, (x0 y1) -> y0 y1) -> forall y1 : a0, (y0 y1) = ((x0 y1) \/ ((y0 y1) /\ (~ (x0 y1)))).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((~ (x0 x2)) \/ (x1 x2)).
Definition term137 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ((x1 y0) /\ (~ (x0 y0))) -> x1 y0.
Definition term361 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x1 x2)) /\ ((~ (x0 x2)) \/ (x1 x2)).
Definition term183 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ ((y0 y2) /\ ((y1 y2) /\ (~ (y0 y2)))))) -> False.
Definition term150 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ (forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2)) -> False.
Definition term81 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ ((forall y2 : a0, (y0 y2) -> y1 y2) -> forall y2 : a0, (y1 y2) = ((y0 y2) \/ ((y1 y2) /\ (~ (y0 y2)))))) -> False.
Definition term327 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term119 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : nat => Peano.le (@CARD a0 x1) y0) (@CARD a0 (@UNION a0 x1 (@DIFF a0 x0 x1))).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0 -> Prop, (@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term170 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (~ (~ (x1 x2))).
Definition term291 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term165 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@INTER a0 x2 (@DIFF a0 x1 x2))).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term347 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) = ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2))))).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) /\ (~ (x1 x2))).
Definition term155 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, (@FINITE a0 y0) /\ (@SUBSET a0 (@DIFF a0 x0 x1) y0).
Definition term163 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 x2) /\ (@IN a0 x0 (@DIFF a0 x1 x2)).
Definition term359 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term162 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@INTER a0 x2 (@DIFF a0 x1 x2)).
Definition term122 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((fun y0 : nat => Peano.le (@CARD a0 x1) y0) (@CARD a0 (@UNION a0 x1 (@DIFF a0 x0 x1)))).
Definition term356 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term345 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Peano.le (@CARD a0 x1) (@CARD a0 (@UNION a0 x1 (@DIFF a0 x0 x1))).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((forall y0 : a0, (x1 y0) -> x0 y0) -> forall y0 : a0, (x0 y0) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0))))).
Definition term123 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop (Peano.le (@CARD a0 x1) (@CARD a0 (@UNION a0 x1 (@DIFF a0 x0 x1)))).
Definition term295 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term172 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0))))).
Definition term228 (x0 : int) (x1 : int) := int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0))).
Definition term263 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term365 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term232 (x0 : int) (x1 : int) := real_add (real_of_int (int_add x0 x1)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term330 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ ((@INTER a0 y0 y1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 y0 y1)) = (Nat.add (@CARD a0 y0) (@CARD a0 y1))) x0.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) x0.
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => Peano.le (@CARD a0 x0) (@CARD a0 y0)) x1.
Definition term364 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)).
Definition term341 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 x0) /\ ((@FINITE a0 y0) /\ ((@INTER a0 x0 y0) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 x0 y0)) = (Nat.add (@CARD a0 x0) (@CARD a0 y0))) x1.
Definition term371 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term355 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term312 := S (Nat.add 0 0).
Definition term256 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term176 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))).
Definition term143 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, ((x1 y0) /\ (~ (x0 y0))) -> x1 y0)).
Definition term157 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @FINITE a0 (@DIFF a0 x0 x1).
Definition term254 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term171 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term138 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a0, ((x1 y0) /\ (~ (x0 y0))) -> x1 y0)) -> False.
Definition term288 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term133 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 (@DIFF a0 x2 x0)) -> @IN a0 x1 x2.
Definition term299 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term187 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, ~ ((x0 y1) /\ ((y0 y1) /\ (~ (x0 y1)))))) -> False) x1.
Definition term154 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, ((x0 y1) /\ (~ (y0 y1))) -> x0 y1)) -> False) x1.
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ ((forall y1 : a0, (x0 y1) -> y0 y1) -> forall y1 : a0, (y0 y1) = ((x0 y1) \/ ((y0 y1) /\ (~ (x0 y1)))))) -> False) x1.
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) = (@IN a0 y0 (@UNION a0 x1 (@DIFF a0 x0 x1))).
Definition term349 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 (@UNION a0 x1 (@DIFF a0 x0 x1))).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (~ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2))))).
Definition term344 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1).
Definition term120 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : nat => Peano.le (@CARD a0 x1) y0) (Nat.add (@CARD a0 x1) (@CARD a0 (@DIFF a0 x0 x1))).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => Peano.le (@CARD a0 x0) (@CARD a0 y0).
Definition term174 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term141 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ((x1 y0) /\ (~ (x0 y0))) -> x1 y0)) -> False) -> (~ (forall y0 : a0, ((x1 y0) /\ (~ (x0 y0))) -> x1 y0)) -> False) -> (~ (forall y0 : a0, ((x1 y0) /\ (~ (x0 y0))) -> x1 y0)) -> False.
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ ((forall y0 : a0, (x1 y0) -> x0 y0) -> forall y0 : a0, (x0 y0) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ ((forall y0 : a0, (x1 y0) -> x0 y0) -> forall y0 : a0, (x0 y0) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ ((forall y0 : a0, (x1 y0) -> x0 y0) -> forall y0 : a0, (x0 y0) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term380 (x0 : int) (x1 : int) := ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x1) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))).
Definition term179 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ (forall y1 : a0, ~ ((x0 y1) /\ ((y0 y1) /\ (~ (x0 y1)))))) -> False.
Definition term146 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ (forall y1 : a0, ((x0 y1) /\ (~ (y0 y1))) -> x0 y1)) -> False.
Definition term77 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ ((forall y1 : a0, (x0 y1) -> y0 y1) -> forall y1 : a0, (y0 y1) = ((x0 y1) \/ ((y0 y1) /\ (~ (x0 y1)))))) -> False.
Definition term320 := real_mul (real_of_num (NUMERAL 0)).
Definition term39 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x1 x2) \/ ((x0 x2) /\ (~ (x1 x2))).
Definition term387 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1).
Definition term82 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (forall y2 : a0, (y0 y2) -> y1 y2) -> forall y2 : a0, (y1 y2) = ((y0 y2) \/ ((y1 y2) /\ (~ (y0 y2)))).
Definition term13 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ ((@INTER a0 y0 y1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 y0 y1)) = (Nat.add (@CARD a0 y0) (@CARD a0 y1)).
Definition term0 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ ((forall y0 : a0, (x1 y0) -> x0 y0) -> forall y0 : a0, (x0 y0) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))).
Definition term278 (x0 : int) := real_sub (real_of_int x0).
Definition term261 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term381 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (int_le (int_of_num (NUMERAL 0)) (int_of_num (@CARD a0 x1))) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num (@CARD a0 (@DIFF a0 x0 x1)))) -> int_le (int_of_num (@CARD a0 x1)) (int_add (int_of_num (@CARD a0 x1)) (int_of_num (@CARD a0 (@DIFF a0 x0 x1)))).
Definition term198 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := int_le (int_of_num (@CARD a0 x1)) (int_add (int_of_num (@CARD a0 x1)) (int_of_num (@CARD a0 (@DIFF a0 x0 x1)))).
Definition term324 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term287 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term10 (a0 : Type') := forall y0 : a0 -> Prop, (exists y1 : a0 -> Prop, (@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))).
Definition term351 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term209 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term194 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := int_of_num (Nat.add (@CARD a0 x1) (@CARD a0 (@DIFF a0 x0 x1))).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term51 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 x2 (@DIFF a0 x1 x2)).
Definition term213 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> int_le x0 (int_add x0 x1).
Definition term181 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ ((y0 y2) /\ ((y1 y2) /\ (~ (y0 y2)))))) -> False.
Definition term148 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2)) -> False.
Definition term79 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ ((forall y2 : a0, (y0 y2) -> y1 y2) -> forall y2 : a0, (y1 y2) = ((y0 y2) \/ ((y1 y2) /\ (~ (y0 y2)))))) -> False.
Definition term226 (x0 : int) (x1 : int) := int_le (int_add (int_add x1 x0) (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term161 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) /\ (@IN a0 x1 x2).
Definition term292 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term383 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := int_of_num (@CARD a0 (@DIFF a0 x0 x1)).
Definition term248 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term214 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term332 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (forall y1 : a0, (x0 y1) -> y0 y1) -> forall y1 : a0, (y0 y1) = ((x0 y1) \/ ((y0 y1) /\ (~ (x0 y1)))).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (~ (x0 y0)) \/ (x1 y0)) x2.
Definition term244 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x1) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term168 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@INTER a0 x1 (@DIFF a0 x0 x1))) = (@IN a0 y0 (@EMPTY a0)).
Definition term130 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@DIFF a0 x1 x0)) -> @IN a0 y0 x1.
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) -> x1 x2.
Definition term268 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term357 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term346 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((x0 x2) \/ (~ (x1 x2))).
Definition term249 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term132 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := imp ((x0 x2) /\ (~ (x1 x2))).
Definition term167 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x1 x2) /\ ((x0 x2) /\ (~ (x1 x2)))).
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 x2) \/ (@IN a0 x0 (@DIFF a0 x1 x2)).
Definition term264 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term270 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term323 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term237 := real_of_num (NUMERAL (BIT1 0)).
Definition term342 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term188 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 (@DIFF a0 x0 x1)) /\ ((@INTER a0 x1 (@DIFF a0 x0 x1)) = (@EMPTY a0)).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (x1 x2).
Definition term215 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term363 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term195 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := int_add (int_of_num (@CARD a0 x1)) (int_of_num (@CARD a0 (@DIFF a0 x0 x1))).
Definition term243 (x0 : int) := and (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term354 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term353 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => Peano.le (@CARD a0 x1) (@CARD a0 y0)) (@UNION a0 x1 (@DIFF a0 x0 x1)).
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (@SUBSET a0 (@DIFF a0 x1 x0) x1).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) /\ (~ (@IN a0 x1 x2)).
Definition term205 (x0 : int) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x1) -> int_le x0 (int_add x0 x1)).
Definition term210 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (~ ((int_le (int_of_num (NUMERAL 0)) x1) -> int_le x0 (int_add x0 x1))).
Definition term297 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (~ (x0 y0)) \/ (x1 y0).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2)))).
Definition term370 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term340 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Nat.add (@CARD a0 x1) (@CARD a0 (@DIFF a0 x0 x1)).
Definition term384 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (int_le (int_of_num (NUMERAL 0)) (int_of_num (@CARD a0 (@DIFF a0 x0 x1)))) -> int_le (int_of_num (@CARD a0 x1)) (int_add (int_of_num (@CARD a0 x1)) (int_of_num (@CARD a0 (@DIFF a0 x0 x1)))).
Definition term360 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term348 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @CARD a0 (@UNION a0 x0 x1).
Definition term225 (x0 : int) (x1 : int) := ~ (int_le x0 (int_add x0 x1)).
Definition term190 (x0 : nat) (x1 : nat) := int_le (int_of_num x0) (int_of_num x1).
Definition term236 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term262 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term135 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@DIFF a0 x1 x0)) -> @IN a0 y0 x1.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0 -> Prop, (@FINITE a0 y0) /\ (@SUBSET a0 x0 y0).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> x1 y0.
Definition term124 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x1) /\ ((@FINITE a0 (@DIFF a0 x0 x1)) /\ ((@INTER a0 x1 (@DIFF a0 x0 x1)) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 x1 (@DIFF a0 x0 x1))) = (Nat.add (@CARD a0 x1) (@CARD a0 (@DIFF a0 x0 x1))).
Definition term182 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, ~ ((y0 y2) /\ ((y1 y2) /\ (~ (y0 y2)))).
Definition term149 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) /\ (~ (y1 y2))) -> y0 y2.
Definition term202 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := int_le (int_of_num (NUMERAL 0)) (int_of_num (@CARD a0 (@DIFF a0 x0 x1))).
Definition term175 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> ((~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term142 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ((x1 y0) /\ (~ (x0 y0))) -> x1 y0)) -> False) -> (~ (forall y0 : a0, ((x1 y0) /\ (~ (x0 y0))) -> x1 y0)) -> False) -> ((~ (forall y0 : a0, ((x1 y0) /\ (~ (x0 y0))) -> x1 y0)) -> False) -> (~ (forall y0 : a0, ((x1 y0) /\ (~ (x0 y0))) -> x1 y0)) -> False.
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ ((forall y0 : a0, (x1 y0) -> x0 y0) -> forall y0 : a0, (x0 y0) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ ((forall y0 : a0, (x1 y0) -> x0 y0) -> forall y0 : a0, (x0 y0) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> ((~ ((forall y0 : a0, (x1 y0) -> x0 y0) -> forall y0 : a0, (x0 y0) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ ((forall y0 : a0, (x1 y0) -> x0 y0) -> forall y0 : a0, (x0 y0) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (x0 y0) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : a0 -> Prop, (@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) x0.
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (~ (x0 y0)) \/ (x1 y0).
Definition term177 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ (forall y1 : a0, ~ ((x0 y1) /\ ((y0 y1) /\ (~ (x0 y1)))))) -> False.
Definition term144 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ (forall y1 : a0, ((x0 y1) /\ (~ (y0 y1))) -> x0 y1)) -> False.
Definition term75 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ ((forall y1 : a0, (x0 y1) -> y0 y1) -> forall y1 : a0, (y0 y1) = ((x0 y1) \/ ((y0 y1) /\ (~ (x0 y1)))))) -> False.
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) -> @IN a0 x1 x2.
Definition term279 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term207 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term53 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := or (@IN a0 x0 x1).
Definition term284 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term192 (x0 : nat) (x1 : nat) := int_of_num (Nat.add x0 x1).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((forall y0 : a0, (x1 y0) -> x0 y0) -> forall y0 : a0, (x0 y0) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term156 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (@SUBSET a0 (@DIFF a0 x0 x1) y0).
Definition term326 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term164 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x1 x2) /\ ((x0 x2) /\ (~ (x1 x2))).
Definition term281 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))))).
Definition term285 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term245 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x1) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Nat.add (@CARD a0 x0) (@CARD a0 x1).
Definition term206 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ (~ (int_le x0 (int_add x0 x1))).
Definition term204 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> int_le x0 (int_add x0 x1).
Definition term338 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term306 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term250 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0) x1.
Definition term220 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term366 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x1 x0) -> x0 = (@UNION a0 x1 (@DIFF a0 x0 x1)).
Definition term257 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term234 (x0 : int) (x1 : int) := real_add (real_of_int (int_add x0 x1)).
Definition term269 := real_div (real_of_num (NUMERAL 0)).
Definition term197 (a0 : Type') (x0 : a0 -> Prop) := int_le (int_of_num (@CARD a0 x0)).
Definition term328 := real_add (real_of_num (NUMERAL 0)).
Definition term212 (x0 : int) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> int_le x0 (int_add x0 x1)).
Definition term378 (x0 : int) (x1 : int) := (~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x1) (real_of_int x0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))))) -> False.
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (~ (x0 x1)).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term240 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0))))).
Definition term139 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, ((x1 y0) /\ (~ (x0 y0))) -> x1 y0).
Definition term100 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((x0 x2) /\ ((~ (x1 x2)) /\ ((~ (x0 x2)) \/ (x1 x2)))).
Definition term147 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ((x0 y1) /\ (~ (y0 y1))) -> x0 y1.
Definition term321 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term233 := int_of_num (NUMERAL (BIT1 0)).
Definition term101 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x0 x2) /\ (~ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2)))))) \/ ((~ (x0 x2)) /\ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2))))).
Definition term11 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> forall y0 : a0 -> Prop, (exists y1 : a0 -> Prop, (@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term98 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ ((~ (x1 x2)) /\ ((~ (x0 x2)) \/ (x1 x2))).
Definition term362 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)).
Definition term201 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) (@CARD a0 (@DIFF a0 x0 x1)).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Peano.le (@CARD a0 x0) (@CARD a0 x1).
Definition term193 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_of_num x1).
Definition term238 := NUMERAL (BIT1 0).
Definition term145 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ((x0 y1) /\ (~ (y0 y1))) -> x0 y1.
Definition term336 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term290 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (x0 x1).
Definition term352 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term343 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term247 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term191 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := int_le (int_of_num (@CARD a0 x1)) (int_of_num (Nat.add (@CARD a0 x1) (@CARD a0 (@DIFF a0 x0 x1)))).
Definition term169 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))).
