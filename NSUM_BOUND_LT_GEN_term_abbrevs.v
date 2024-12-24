Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term312 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.lt x0 y0) /\ (Peano.le y0 x1).
Definition term184 (x0 : int) (x1 : int) := (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))).
Definition term247 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term402 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term265 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term209 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term110 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term354 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (@IN a0 x2 x0) -> Peano.lt (x1 x2) (Nat.add (x1 x2) (NUMERAL (BIT1 0))).
Definition term34 (x0 : int) (x1 : int) := (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) \/ (~ (int_lt x0 x1)).
Definition term15 (x0 : nat) (x1 : nat) := int_lt (int_of_num x0) (int_of_num x1).
Definition term122 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term348 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := @eq nat ((fun y0 : a0 => Nat.add (x0 y0) (NUMERAL (BIT1 0))) x1).
Definition term253 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term412 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : nat) (x3 : a0 -> Prop) := (@IN a0 x1 x3) -> Peano.lt (x0 x1) (Nat.div x2 (@CARD a0 x3)).
Definition term50 (x0 : int) (x1 : int) := (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) /\ (int_lt x0 x1).
Definition term74 (x0 : int) (x1 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_add x1 (int_of_num (NUMERAL (BIT1 0))))).
Definition term159 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term181 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term399 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term187 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term242 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term167 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term310 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) /\ (Peano.le x1 x2).
Definition term243 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term251 (x0 : int) := real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term345 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := Nat.add (x0 x1) (NUMERAL (BIT1 0)).
Definition term109 (x0 : nat) := real_neg (real_of_num x0).
Definition term42 (x0 : int) (x1 : int) := ~ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) /\ (~ (int_lt x0 x1))).
Definition term66 := real_of_int (int_of_num (NUMERAL 0)).
Definition term420 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : nat) (x3 : a0 -> Prop) := (@IN a0 x1 x3) -> Peano.le ((fun y0 : a0 => Nat.add (x0 y0) (NUMERAL (BIT1 0))) x1) (Nat.div x2 (@CARD a0 x3)).
Definition term99 (x0 : Prop) := ~ (~ x0).
Definition term67 := real_of_num (NUMERAL 0).
Definition term304 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) x0.
Definition term391 (x0 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term19 (x0 : nat) (x1 : nat) := or ((int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_lt (int_of_num x0) (int_of_num x1))).
Definition term89 (x0 : int) (x1 : int) := (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) \/ (real_le (real_of_int x0) (real_of_int x1)).
Definition term252 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term60 (x0 : int) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) /\ (int_lt x0 x1)) \/ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) /\ (~ (int_lt x0 x1)))).
Definition term175 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term101 (x0 : int) (x1 : int) := ((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) \/ (real_le (real_of_int x1) (real_of_int x0))) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term64 := int_of_num (NUMERAL 0).
Definition term365 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := int_lt (int_of_num (x0 x1)) (int_of_num (Nat.add (x0 x1) (NUMERAL (BIT1 0)))).
Definition term11 (x0 : nat) := int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))).
Definition term405 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : int) := ((~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ ((@IN a0 x0 x1) /\ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)))))) -> False) -> ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ ((@IN a0 x0 x1) /\ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)))).
Definition term271 (x0 : int) (x1 : int) := ((~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) \/ (real_le (real_of_int x1) (real_of_int x0))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))))))) -> False) -> ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) \/ (real_le (real_of_int x1) (real_of_int x0))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))))).
Definition term28 (x0 : nat) (x1 : nat) := ((int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_lt (int_of_num x0) (int_of_num x1))) \/ ((~ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) /\ (~ (int_lt (int_of_num x0) (int_of_num x1)))).
Definition term241 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term165 := ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term245 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term169 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term397 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term185 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term317 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.lt y0 y2) /\ (Peano.le y2 y1)) -> Peano.lt y0 y1.
Definition term182 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x0) (real_of_int x1)).
Definition term425 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term153 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term261 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term36 (x0 : int) (x1 : int) := ~ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term387 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x2) /\ (~ ((~ (@IN a0 x0 x1)) \/ (int_lt x2 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))))).
Definition term376 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : int) := ~ (~ ((int_le (int_of_num (NUMERAL 0)) x2) -> (~ (@IN a0 x0 x1)) \/ (int_lt x2 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))))).
Definition term31 (x0 : int) (x1 : int) := ~ (~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) /\ (int_lt x0 x1)) \/ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) /\ (~ (int_lt x0 x1))))).
Definition term362 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (~ (@IN a0 x2 x0)) \/ (Peano.lt (x1 x2) (Nat.add (x1 x2) (NUMERAL (BIT1 0)))).
Definition term339 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := ((@IN a0 x1 x2) = (@IN a0 x1 x2)) -> ((@IN a0 x1 x2) -> (Peano.lt (x0 x1) ((fun y0 : a0 => Nat.add (x0 y0) (NUMERAL (BIT1 0))) x1)) = x3) -> ((@IN a0 x1 x2) -> Peano.lt (x0 x1) ((fun y0 : a0 => Nat.add (x0 y0) (NUMERAL (BIT1 0))) x1)) = ((@IN a0 x1 x2) -> x3).
Definition term199 (x0 : int) (x1 : int) := (real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))))).
Definition term437 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> nat, forall y2 : nat, ((@FINITE a0 y0) /\ ((~ (y0 = (@EMPTY a0))) /\ (forall y3 : a0, (@IN a0 y3 y0) -> Peano.lt (y1 y3) (Nat.div y2 (@CARD a0 y0))))) -> Peano.lt (@nsum a0 y0 y1) y2.
Definition term298 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, forall y2 : a0 -> nat, ((@FINITE a0 y1) /\ ((~ (y1 = (@EMPTY a0))) /\ (forall y3 : a0, (@IN a0 y3 y1) -> Peano.lt (y0 y3) (y2 y3)))) -> Peano.lt (@nsum a0 y1 y0) (@nsum a0 y1 y2).
Definition term286 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ ((~ (y2 = (@EMPTY a0))) /\ (forall y3 : a0, (@IN a0 y3 y2) -> Peano.lt (y0 y3) (y1 y3)))) -> Peano.lt (@nsum a0 y2 y0) (@nsum a0 y2 y1).
Definition term275 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> nat, forall y2 : nat, ((@FINITE a0 y0) /\ ((~ (y0 = (@EMPTY a0))) /\ (forall y3 : a0, (@IN a0 y3 y0) -> Peano.le (y1 y3) (Nat.div y2 (@CARD a0 y0))))) -> Peano.le (@nsum a0 y0 y1) y2.
Definition term117 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term139 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term360 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := True /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.lt (x1 y0) (Nat.add (x1 y0) (NUMERAL (BIT1 0)))).
Definition term53 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ (~ (((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) /\ (int_lt x0 x1)) \/ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) /\ (~ (int_lt x0 x1))))).
Definition term234 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term334 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := Peano.lt (x0 x1) ((fun y0 : a0 => Nat.add (x0 y0) (NUMERAL (BIT1 0))) x1).
Definition term77 (x0 : int) := real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term55 (x0 : int) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x1) -> ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) /\ (int_lt x0 x1)) \/ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) /\ (~ (int_lt x0 x1)))).
Definition term435 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := forall y0 : nat, ((@FINITE a0 x0) /\ ((~ (x0 = (@EMPTY a0))) /\ (forall y1 : a0, (@IN a0 y1 x0) -> Peano.lt (x1 y1) (Nat.div y0 (@CARD a0 x0))))) -> Peano.lt (@nsum a0 x0 x1) y0.
Definition term279 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := forall y0 : nat, ((@FINITE a0 x0) /\ ((~ (x0 = (@EMPTY a0))) /\ (forall y1 : a0, (@IN a0 y1 x0) -> Peano.le (x1 y1) (Nat.div y0 (@CARD a0 x0))))) -> Peano.le (@nsum a0 x0 x1) y0.
Definition term98 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) \/ (real_le (real_of_int x1) (real_of_int x0))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))))).
Definition term131 (x0 : int) := real_ge (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term395 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ ((@IN a0 x0 x1) /\ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2))).
Definition term390 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : int) := (~ (@IN a0 x0 x1)) \/ (int_lt x2 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))).
Definition term424 (a0 : Type') := forall y0 : a0, True.
Definition term300 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, forall y2 : a0 -> nat, ((@FINITE a0 y1) /\ ((~ (y1 = (@EMPTY a0))) /\ (forall y3 : a0, (@IN a0 y3 y1) -> Peano.lt (y0 y3) (y2 y3)))) -> Peano.lt (@nsum a0 y1 y0) (@nsum a0 y1 y2)) x0.
Definition term287 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ ((~ (y2 = (@EMPTY a0))) /\ (forall y3 : a0, (@IN a0 y3 y2) -> Peano.lt (y0 y3) (y1 y3)))) -> Peano.lt (@nsum a0 y2 y0) (@nsum a0 y2 y1)) x0.
Definition term276 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> nat, forall y2 : nat, ((@FINITE a0 y0) /\ ((~ (y0 = (@EMPTY a0))) /\ (forall y3 : a0, (@IN a0 y3 y0) -> Peano.le (y1 y3) (Nat.div y2 (@CARD a0 y0))))) -> Peano.le (@nsum a0 y0 y1) y2) x0.
Definition term177 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term400 (x0 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term188 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term168 (x0 : nat) := real_add (real_of_num x0) (real_neg (real_of_num x0)).
Definition term302 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (fun y0 : a0 -> nat => ((@FINITE a0 x1) /\ ((~ (x1 = (@EMPTY a0))) /\ (forall y1 : a0, (@IN a0 y1 x1) -> Peano.lt (x0 y1) (y0 y1)))) -> Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 y0)) x2.
Definition term291 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ ((~ (y0 = (@EMPTY a0))) /\ (forall y1 : a0, (@IN a0 y1 y0) -> Peano.lt (x0 y1) (x1 y1)))) -> Peano.lt (@nsum a0 y0 x0) (@nsum a0 y0 x1)) x2.
Definition term223 (x0 : int) (x1 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term423 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x2) -> Peano.le ((fun y1 : a0 => Nat.add (x0 y1) (NUMERAL (BIT1 0))) y0) (Nat.div x1 (@CARD a0 x2)).
Definition term358 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := forall y0 : a0, (@IN a0 y0 x0) -> Peano.lt (x1 y0) (Nat.add (x1 y0) (NUMERAL (BIT1 0))).
Definition term322 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x2) -> Peano.lt (x0 y0) (Nat.div x1 (@CARD a0 x2)).
Definition term266 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term357 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := forall y0 : a0, (@IN a0 y0 x0) -> Peano.lt (x1 y0) ((fun y1 : a0 => Nat.add (x1 y1) (NUMERAL (BIT1 0))) y0).
Definition term239 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term238 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term163 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term158 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term136 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term283 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := Peano.le (@nsum a0 x0 x1) x2.
Definition term150 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term108 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term344 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (fun y0 : a0 => Nat.add (x0 y0) (NUMERAL (BIT1 0))) x1.
Definition term94 (x0 : int) (x1 : int) := and ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) \/ (real_le (real_of_int x0) (real_of_int x1))).
Definition term228 (x0 : int) (x1 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))) (real_of_num (NUMERAL 0)).
Definition term70 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term315 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.lt x0 y1) /\ (Peano.le y1 y0)) -> Peano.lt x0 y0.
Definition term176 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term299 (a0 : Type') := (forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ ((~ (y2 = (@EMPTY a0))) /\ (forall y3 : a0, (@IN a0 y3 y2) -> Peano.lt (y0 y3) (y1 y3)))) -> Peano.lt (@nsum a0 y2 y0) (@nsum a0 y2 y1)) -> forall y0 : a0 -> nat, forall y1 : a0 -> Prop, forall y2 : a0 -> nat, ((@FINITE a0 y1) /\ ((~ (y1 = (@EMPTY a0))) /\ (forall y3 : a0, (@IN a0 y3 y1) -> Peano.lt (y0 y3) (y2 y3)))) -> Peano.lt (@nsum a0 y1 y0) (@nsum a0 y1 y2).
Definition term285 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> nat, forall y2 : nat, ((@FINITE a0 y0) /\ ((~ (y0 = (@EMPTY a0))) /\ (forall y3 : a0, (@IN a0 y3 y0) -> Peano.le (y1 y3) (Nat.div y2 (@CARD a0 y0))))) -> Peano.le (@nsum a0 y0 y1) y2) -> forall y0 : a0 -> Prop, forall y1 : a0 -> nat, forall y2 : nat, ((@FINITE a0 y0) /\ ((~ (y0 = (@EMPTY a0))) /\ (forall y3 : a0, (@IN a0 y3 y0) -> Peano.le (y1 y3) (Nat.div y2 (@CARD a0 y0))))) -> Peano.le (@nsum a0 y0 y1) y2.
Definition term130 (x0 : int) := real_ge (real_of_int x0).
Definition term134 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term385 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term90 (x0 : int) (x1 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x1).
Definition term143 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term71 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term222 (x0 : int) (x1 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term217 (x0 : int) (x1 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))) (real_of_num (NUMERAL 0)).
Definition term371 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (~ (@IN a0 x2 x0)) \/ (int_lt (int_of_num (x1 x2)) (int_add (int_of_num (x1 x2)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term112 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term86 (x0 : int) (x1 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term194 (x0 : int) (x1 : int) := ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term200 (x0 : int) (x1 : int) := ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))))).
Definition term259 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term40 (x0 : int) (x1 : int) := (~ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))) \/ (~ (~ (int_lt x0 x1))).
Definition term59 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) \/ (~ (int_lt x0 x1))) /\ ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) \/ (int_lt x0 x1)))).
Definition term146 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term129 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term161 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term411 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => (@IN a0 y0 x2) -> Peano.lt (x0 y0) (Nat.div x1 (@CARD a0 x2))) x3.
Definition term280 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := (fun y0 : nat => ((@FINITE a0 x0) /\ ((~ (x0 = (@EMPTY a0))) /\ (forall y1 : a0, (@IN a0 y1 x0) -> Peano.le (x1 y1) (Nat.div y0 (@CARD a0 x0))))) -> Peano.le (@nsum a0 x0 x1) y0) x2.
Definition term41 (x0 : int) (x1 : int) := (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) \/ (int_lt x0 x1).
Definition term78 (x0 : int) := real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term124 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term260 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term195 (x0 : int) := and (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term368 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := int_lt (int_of_num (x0 x1)).
Definition term393 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term347 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := @eq nat ((fun y0 : a0 => (fun y1 : a0 => Nat.add (x0 y1) (NUMERAL (BIT1 0))) y0) x1).
Definition term335 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN a0 x2 x0) = y0) -> (y0 -> (Peano.lt (x1 x2) ((fun y2 : a0 => Nat.add (x1 y2) (NUMERAL (BIT1 0))) x2)) = y1) -> ((@IN a0 x2 x0) -> Peano.lt (x1 x2) ((fun y2 : a0 => Nat.add (x1 y2) (NUMERAL (BIT1 0))) x2)) = (y0 -> y1)) x3.
Definition term91 (x0 : int) (x1 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1).
Definition term281 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := ((@FINITE a0 x0) /\ ((~ (x0 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) (Nat.div x2 (@CARD a0 x0))))) -> Peano.le (@nsum a0 x0 x1) x2.
Definition term116 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term264 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term102 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) \/ (real_le (real_of_int x1) (real_of_int x0))) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term398 (x0 : int) := real_sub (real_of_int x0) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term186 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term205 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))))).
Definition term197 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))))).
Definition term240 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term164 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term273 (x0 : nat) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x0)) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) -> ((int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_lt (int_of_num x0) (int_of_num x1))) \/ ((~ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) /\ (~ (int_lt (int_of_num x0) (int_of_num x1)))).
Definition term237 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term178 (x0 : int) (x1 : int) := real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term128 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term306 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1) x1.
Definition term301 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> nat, ((@FINITE a0 y0) /\ ((~ (y0 = (@EMPTY a0))) /\ (forall y2 : a0, (@IN a0 y2 y0) -> Peano.lt (x0 y2) (y1 y2)))) -> Peano.lt (@nsum a0 y0 x0) (@nsum a0 y0 y1)) x1.
Definition term289 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((~ (y1 = (@EMPTY a0))) /\ (forall y2 : a0, (@IN a0 y2 y1) -> Peano.lt (x0 y2) (y0 y2)))) -> Peano.lt (@nsum a0 y1 x0) (@nsum a0 y1 y0)) x1.
Definition term278 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : nat, ((@FINITE a0 x0) /\ ((~ (x0 = (@EMPTY a0))) /\ (forall y2 : a0, (@IN a0 y2 x0) -> Peano.le (y0 y2) (Nat.div y1 (@CARD a0 x0))))) -> Peano.le (@nsum a0 x0 y0) y1) x1.
Definition term352 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := ((@IN a0 x2 x0) -> (Peano.lt (x1 x2) ((fun y0 : a0 => Nat.add (x1 y0) (NUMERAL (BIT1 0))) x2)) = (Peano.lt (x1 x2) (Nat.add (x1 x2) (NUMERAL (BIT1 0))))) -> ((@IN a0 x2 x0) -> Peano.lt (x1 x2) ((fun y0 : a0 => Nat.add (x1 y0) (NUMERAL (BIT1 0))) x2)) = ((@IN a0 x2 x0) -> Peano.lt (x1 x2) (Nat.add (x1 x2) (NUMERAL (BIT1 0)))).
Definition term180 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)).
Definition term69 := real_le (real_of_num (NUMERAL 0)).
Definition term75 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term267 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term196 (x0 : int) (x1 : int) := (real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term207 := real_lt (real_of_num (NUMERAL 0)).
Definition term356 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := fun y0 : a0 => (@IN a0 y0 x0) -> Peano.lt (x1 y0) (Nat.add (x1 y0) (NUMERAL (BIT1 0))).
Definition term179 (x0 : int) (x1 : int) := real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)).
Definition term82 (x0 : int) := real_add (real_of_int x0).
Definition term29 (x0 : nat) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) x0.
Definition term328 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term396 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : int) := ~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ ((@IN a0 x0 x1) /\ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2))))).
Definition term100 (x0 : int) (x1 : int) := ~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) \/ (real_le (real_of_int x1) (real_of_int x0))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))))))).
Definition term330 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term220 (x0 : int) (x1 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term214 (x0 : int) (x1 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))).
Definition term192 (x0 : int) (x1 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term269 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term233 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term65 (x0 : nat) := real_of_int (int_of_num x0).
Definition term338 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) (x4 : Prop) := ((@IN a0 x2 x0) = x3) -> (x3 -> (Peano.lt (x1 x2) ((fun y0 : a0 => Nat.add (x1 y0) (NUMERAL (BIT1 0))) x2)) = x4) -> ((@IN a0 x2 x0) -> Peano.lt (x1 x2) ((fun y0 : a0 => Nat.add (x1 y0) (NUMERAL (BIT1 0))) x2)) = (x3 -> x4).
Definition term87 (x0 : int) (x1 : int) := or (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term351 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (@IN a0 x2 x0) -> (Peano.lt (x1 x2) ((fun y0 : a0 => Nat.add (x1 y0) (NUMERAL (BIT1 0))) x2)) = (Peano.lt (x1 x2) (Nat.add (x1 x2) (NUMERAL (BIT1 0)))).
Definition term172 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term381 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term294 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term413 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := Peano.le ((fun y0 : a0 => Nat.add (x0 y0) (NUMERAL (BIT1 0))) x1).
Definition term244 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term123 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term355 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := fun y0 : a0 => (@IN a0 y0 x0) -> Peano.lt (x1 y0) ((fun y1 : a0 => Nat.add (x1 y1) (NUMERAL (BIT1 0))) y0).
Definition term308 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.lt x1 x0) /\ (Peano.le x0 y0)) -> Peano.lt x1 y0) x2.
Definition term35 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term76 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term25 (x0 : nat) (x1 : nat) := ~ (int_lt (int_of_num x0) (int_of_num x1)).
Definition term235 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term314 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.lt x0 y0) /\ (Peano.le y0 x1)) -> Peano.lt x0 x1.
Definition term115 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term103 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) \/ (real_le (real_of_int x1) (real_of_int x0))) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))).
Definition term268 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term144 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term204 (x0 : int) (x1 : int) := (real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term160 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term430 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := exists y0 : nat, (Peano.lt (@nsum a0 x0 x1) y0) /\ (Peano.le y0 x2).
Definition term152 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term72 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_add x1 (int_of_num (NUMERAL (BIT1 0)))).
Definition term341 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term232 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0).
Definition term47 (x0 : int) (x1 : int) := (~ ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) /\ (int_lt x0 x1))) /\ (~ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) /\ (~ (int_lt x0 x1)))).
Definition term329 (a0 : Type') (x0 : a0 -> Prop) := and (~ (x0 = (@EMPTY a0))).
Definition term429 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := (Peano.lt (@nsum a0 x0 x1) (@nsum a0 x0 (fun y0 : a0 => Nat.add (x1 y0) (NUMERAL (BIT1 0))))) /\ (Peano.le (@nsum a0 x0 (fun y0 : a0 => Nat.add (x1 y0) (NUMERAL (BIT1 0)))) x2).
Definition term61 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) /\ (int_lt x0 x1)) \/ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) /\ (~ (int_lt x0 x1))).
Definition term316 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.lt y0 y2) /\ (Peano.le y2 y1)) -> Peano.lt y0 y1.
Definition term305 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1.
Definition term303 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2.
Definition term415 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := Nat.div x0 (@CARD a0 x1).
Definition term254 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term422 (a0 : Type') := fun y0 : a0 => True.
Definition term85 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term342 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term17 (x0 : nat) (x1 : nat) := (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_lt (int_of_num x0) (int_of_num x1)).
Definition term417 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : nat) (x3 : a0 -> Prop) := Peano.le (Nat.add (x0 x1) (NUMERAL (BIT1 0))) (Nat.div x2 (@CARD a0 x3)).
Definition term141 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term132 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term57 (x0 : int) (x1 : int) := ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) /\ (int_lt x0 x1)) \/ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) /\ (~ (int_lt x0 x1))).
Definition term1 (x0 : nat) (x1 : nat) := ((Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1) /\ (Peano.lt x0 x1)) \/ ((~ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1)) /\ (~ (Peano.lt x0 x1))).
Definition term46 (x0 : int) (x1 : int) := and ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) \/ (~ (int_lt x0 x1))).
Definition term22 (x0 : nat) (x1 : nat) := and (~ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1)).
Definition term226 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term215 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term426 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0 -> Prop) := (~ (x2 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x2) -> Peano.le ((fun y1 : a0 => Nat.add (x0 y1) (NUMERAL (BIT1 0))) y0) (Nat.div x1 (@CARD a0 x2))).
Definition term359 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := (~ (x0 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.lt (x1 y0) ((fun y1 : a0 => Nat.add (x1 y1) (NUMERAL (BIT1 0))) y0)).
Definition term321 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0 -> Prop) := (~ (x2 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x2) -> Peano.lt (x0 y0) (Nat.div x1 (@CARD a0 x2))).
Definition term323 (a0 : Type') (x0 : a0 -> Prop) := ~ (x0 = (@EMPTY a0)).
Definition term410 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := ((@FINITE a0 x0) /\ ((~ (x0 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le ((fun y1 : a0 => Nat.add (x1 y1) (NUMERAL (BIT1 0))) y0) (Nat.div x2 (@CARD a0 x0))))) -> Peano.le (@nsum a0 x0 (fun y0 : a0 => Nat.add (x1 y0) (NUMERAL (BIT1 0)))) x2.
Definition term145 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term12 (x0 : nat) (x1 : nat) := int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1).
Definition term389 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x2) -> (~ (@IN a0 x0 x1)) \/ (int_lt x2 (int_add x2 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term93 (x0 : int) (x1 : int) := (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term231 (x0 : int) := real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term33 (x0 : int) (x1 : int) := ~ ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) /\ (int_lt x0 x1)).
Definition term219 (x0 : int) (x1 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))).
Definition term120 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term257 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term407 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (int_le (int_of_num (NUMERAL 0)) (int_of_num (x1 x2))) -> (~ (@IN a0 x2 x0)) \/ (int_lt (int_of_num (x1 x2)) (int_add (int_of_num (x1 x2)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term372 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := fun y0 : a0 => (~ (@IN a0 y0 x0)) \/ (int_lt (int_of_num (x1 y0)) (int_add (int_of_num (x1 y0)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term4 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term401 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term190 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term211 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term26 (x0 : nat) (x1 : nat) := (~ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1)) /\ (~ (Peano.lt x0 x1)).
Definition term263 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term73 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term162 := S (Nat.add 0 0).
Definition term113 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term149 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term374 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) (x0 x1).
Definition term14 (x0 : nat) (x1 : nat) := and (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)).
Definition term378 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (~ (@IN a0 x0 x1)).
Definition term189 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term88 (x0 : int) (x1 : int) := or (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term111 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term203 (x0 : int) (x1 : int) := ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))))) \/ ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))))).
Definition term138 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term336 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) := forall y0 : Prop, ((@IN a0 x2 x0) = x3) -> (x3 -> (Peano.lt (x1 x2) ((fun y1 : a0 => Nat.add (x1 y1) (NUMERAL (BIT1 0))) x2)) = y0) -> ((@IN a0 x2 x0) -> Peano.lt (x1 x2) ((fun y1 : a0 => Nat.add (x1 y1) (NUMERAL (BIT1 0))) x2)) = (x3 -> y0).
Definition term331 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term353 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (@IN a0 x2 x0) -> Peano.lt (x1 x2) ((fun y0 : a0 => Nat.add (x1 y0) (NUMERAL (BIT1 0))) x2).
Definition term45 (x0 : int) (x1 : int) := and (~ ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) /\ (int_lt x0 x1))).
Definition term13 (x0 : nat) (x1 : nat) := and (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1).
Definition term8 (x0 : nat) := int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0))).
Definition term225 (x0 : int) (x1 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))).
Definition term201 (x0 : int) (x1 : int) := (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term414 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := Peano.le (Nat.add (x0 x1) (NUMERAL (BIT1 0))).
Definition term386 (x0 : int) := int_lt x0 (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term224 (x0 : int) (x1 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))).
Definition term369 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := int_lt (int_of_num (x0 x1)) (int_add (int_of_num (x0 x1)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term170 := real_mul (real_of_num (NUMERAL 0)).
Definition term155 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term333 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := forall y0 : Prop, forall y1 : Prop, ((@IN a0 x2 x0) = y0) -> (y0 -> (Peano.lt (x1 x2) ((fun y2 : a0 => Nat.add (x1 y2) (NUMERAL (BIT1 0))) x2)) = y1) -> ((@IN a0 x2 x0) -> Peano.lt (x1 x2) ((fun y2 : a0 => Nat.add (x1 y2) (NUMERAL (BIT1 0))) x2)) = (y0 -> y1).
Definition term332 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term295 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ ((~ (y2 = (@EMPTY a0))) /\ (forall y3 : a0, (@IN a0 y3 y2) -> Peano.lt (y0 y3) (y1 y3)))) -> Peano.lt (@nsum a0 y2 y0) (@nsum a0 y2 y1)) -> Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term419 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term340 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := ((@IN a0 x1 x2) -> (Peano.lt (x0 x1) ((fun y0 : a0 => Nat.add (x0 y0) (NUMERAL (BIT1 0))) x1)) = x3) -> ((@IN a0 x1 x2) -> Peano.lt (x0 x1) ((fun y0 : a0 => Nat.add (x0 y0) (NUMERAL (BIT1 0))) x1)) = ((@IN a0 x1 x2) -> x3).
Definition term380 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (~ (~ (@IN a0 x0 x1))).
Definition term307 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt x1 x0) /\ (Peano.le x0 y0)) -> Peano.lt x1 y0.
Definition term84 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term54 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ (((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) \/ (~ (int_lt x0 x1))) /\ ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) \/ (int_lt x0 x1))).
Definition term433 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := Peano.lt (@nsum a0 x0 x1) x2.
Definition term436 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> nat, forall y1 : nat, ((@FINITE a0 x0) /\ ((~ (x0 = (@EMPTY a0))) /\ (forall y2 : a0, (@IN a0 y2 x0) -> Peano.lt (y0 y2) (Nat.div y1 (@CARD a0 x0))))) -> Peano.lt (@nsum a0 x0 y0) y1.
Definition term297 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> Prop, forall y1 : a0 -> nat, ((@FINITE a0 y0) /\ ((~ (y0 = (@EMPTY a0))) /\ (forall y2 : a0, (@IN a0 y2 y0) -> Peano.lt (x0 y2) (y1 y2)))) -> Peano.lt (@nsum a0 y0 x0) (@nsum a0 y0 y1).
Definition term288 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((~ (y1 = (@EMPTY a0))) /\ (forall y2 : a0, (@IN a0 y2 y1) -> Peano.lt (x0 y2) (y0 y2)))) -> Peano.lt (@nsum a0 y1 x0) (@nsum a0 y1 y0).
Definition term277 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> nat, forall y1 : nat, ((@FINITE a0 x0) /\ ((~ (x0 = (@EMPTY a0))) /\ (forall y2 : a0, (@IN a0 y2 x0) -> Peano.le (y0 y2) (Nat.div y1 (@CARD a0 x0))))) -> Peano.le (@nsum a0 x0 y0) y1.
Definition term377 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x2) -> (~ (@IN a0 x0 x1)) \/ (int_lt x2 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))).
Definition term379 (x0 : int) := ~ (int_lt x0 (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term361 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := (@FINITE a0 x0) /\ ((~ (x0 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.lt (x1 y0) ((fun y1 : a0 => Nat.add (x1 y1) (NUMERAL (BIT1 0))) y0))).
Definition term293 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := (@FINITE a0 x0) /\ ((~ (x0 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.lt (x1 y0) (x2 y0))).
Definition term218 (x0 : int) (x1 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term408 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := int_of_num (x0 x1).
Definition term30 (x0 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term118 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term174 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term337 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((@IN a0 x2 x0) = x3) -> (x3 -> (Peano.lt (x1 x2) ((fun y1 : a0 => Nat.add (x1 y1) (NUMERAL (BIT1 0))) x2)) = y0) -> ((@IN a0 x2 x0) -> Peano.lt (x1 x2) ((fun y1 : a0 => Nat.add (x1 y1) (NUMERAL (BIT1 0))) x2)) = (x3 -> y0)) x4.
Definition term366 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := int_of_num (Nat.add (x0 x1) (NUMERAL (BIT1 0))).
Definition term311 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> Peano.lt x0 x1.
Definition term137 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term382 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : int) := (~ (~ (@IN a0 x0 x1))) /\ (~ (int_lt x2 (int_add x2 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term227 (x0 : int) (x1 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))) (real_of_num (NUMERAL 0)).
Definition term221 (x0 : int) (x1 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term216 (x0 : int) (x1 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))) (real_of_num (NUMERAL 0)).
Definition term52 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term373 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := forall y0 : a0, (~ (@IN a0 y0 x0)) \/ (int_lt (int_of_num (x1 y0)) (int_add (int_of_num (x1 y0)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term364 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := forall y0 : a0, (~ (@IN a0 y0 x0)) \/ (Peano.lt (x1 y0) (Nat.add (x1 y0) (NUMERAL (BIT1 0)))).
Definition term193 (x0 : int) (x1 : int) := and ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)))).
Definition term24 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term375 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := int_le (int_of_num (NUMERAL 0)) (int_of_num (x0 x1)).
Definition term326 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 => Nat.add (x0 y0) (NUMERAL (BIT1 0)).
Definition term230 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_add (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term97 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) \/ (real_le (real_of_int x1) (real_of_int x0))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))).
Definition term324 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := (exists y0 : nat, (Peano.lt (@nsum a0 x0 x1) y0) /\ (Peano.le y0 x2)) -> Peano.lt (@nsum a0 x0 x1) x2.
Definition term3 (x0 : nat) (x1 : nat) := int_le (int_of_num (Nat.add x0 (NUMERAL (BIT1 0)))) (int_of_num x1).
Definition term142 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term346 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 => (fun y1 : a0 => Nat.add (x0 y1) (NUMERAL (BIT1 0))) y0.
Definition term416 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : nat) (x3 : a0 -> Prop) := Peano.le ((fun y0 : a0 => Nat.add (x0 y0) (NUMERAL (BIT1 0))) x1) (Nat.div x2 (@CARD a0 x3)).
Definition term349 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := Peano.lt (x0 x1).
Definition term105 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term62 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term318 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.lt y0 y2) /\ (Peano.le y2 y1)) -> Peano.lt y0 y1) x0.
Definition term434 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := ((@FINITE a0 x0) /\ ((~ (x0 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.lt (x1 y0) (Nat.div x2 (@CARD a0 x0))))) -> Peano.lt (@nsum a0 x0 x1) x2.
Definition term256 (x0 : int) (x1 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))).
Definition term403 (a0 : Type') (x0 : int) (x1 : a0) (x2 : a0 -> Prop) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((@IN a0 x1 x2) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term191 (x0 : int) (x1 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term394 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : int) := (@IN a0 x0 x1) /\ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)).
Definition term58 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (~ ((int_le (int_of_num (NUMERAL 0)) x1) -> ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) /\ (int_lt x0 x1)) \/ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) /\ (~ (int_lt x0 x1))))).
Definition term125 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term18 (x0 : nat) (x1 : nat) := or ((Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1) /\ (Peano.lt x0 x1)).
Definition term106 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term383 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : int) := (@IN a0 x0 x1) /\ (~ (int_lt x2 (int_add x2 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term48 (x0 : int) (x1 : int) := ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) \/ (~ (int_lt x0 x1))) /\ ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) \/ (int_lt x0 x1)).
Definition term121 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term49 (x0 : int) (x1 : int) := ~ (((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) /\ (int_lt x0 x1)) \/ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) /\ (~ (int_lt x0 x1)))).
Definition term127 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term309 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x1 x0) /\ (Peano.le x0 x2)) -> Peano.lt x1 x2.
Definition term173 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term81 := real_of_num (NUMERAL (BIT1 0)).
Definition term212 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term284 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := (forall y0 : a0 -> Prop, forall y1 : a0 -> nat, forall y2 : nat, ((@FINITE a0 y0) /\ ((~ (y0 = (@EMPTY a0))) /\ (forall y3 : a0, (@IN a0 y3 y0) -> Peano.le (y1 y3) (Nat.div y2 (@CARD a0 y0))))) -> Peano.le (@nsum a0 y0 y1) y2) -> Peano.le (@nsum a0 x0 x1) x2.
Definition term272 (x0 : int) (x1 : int) := ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) \/ (real_le (real_of_int x1) (real_of_int x0))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))))).
Definition term63 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term418 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : nat) (x3 : a0 -> Prop) := Peano.lt (x0 x1) (Nat.div x2 (@CARD a0 x3)).
Definition term255 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term96 (x0 : int) := and (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term51 (x0 : int) (x1 : int) := (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) /\ (~ (int_lt x0 x1)).
Definition term154 := real_add (real_of_num (NUMERAL (BIT1 0))).
Definition term156 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term23 (x0 : nat) (x1 : nat) := and (~ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))).
Definition term32 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> ((int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1) /\ (int_lt x0 x1)) \/ ((~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) /\ (~ (int_lt x0 x1))).
Definition term388 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : int) := (int_le (int_of_num (NUMERAL 0)) x2) /\ ((@IN a0 x0 x1) /\ (~ (int_lt x2 (int_add x2 (int_of_num (NUMERAL (BIT1 0))))))).
Definition term147 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term262 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term210 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term432 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @nsum a0 x0 (fun y0 : a0 => Nat.add (x1 y0) (NUMERAL (BIT1 0))).
Definition term148 (x0 : int) := real_add (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term37 (x0 : int) (x1 : int) := ~ (~ (int_lt x0 x1)).
Definition term198 (x0 : int) (x1 : int) := ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term327 (a0 : Type') (x0 : a0 -> Prop) := (~ (x0 = (@EMPTY a0))) -> (x0 = (@EMPTY a0)) = False.
Definition term202 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))))).
Definition term21 (x0 : nat) (x1 : nat) := ~ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)).
Definition term27 (x0 : nat) (x1 : nat) := (~ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) /\ (~ (int_lt (int_of_num x0) (int_of_num x1))).
Definition term2 (x0 : nat) (x1 : nat) := int_le (int_of_num x0) (int_of_num x1).
Definition term80 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term313 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.lt x0 y0) /\ (Peano.le y0 x1).
Definition term119 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term92 (x0 : int) (x1 : int) := or (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term16 (x0 : nat) (x1 : nat) := (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1) /\ (Peano.lt x0 x1).
Definition term7 (x0 : nat) := int_of_num (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term409 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := Peano.lt (@nsum a0 x0 x1) (@nsum a0 x0 (fun y0 : a0 => Nat.add (x1 y0) (NUMERAL (BIT1 0)))).
Definition term292 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := ((@FINITE a0 x1) /\ ((~ (x1 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x1) -> Peano.lt (x0 y0) (x2 y0)))) -> Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term56 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term431 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := fun y0 : nat => (Peano.lt (@nsum a0 x0 x1) y0) /\ (Peano.le y0 x2).
Definition term83 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term166 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term5 (x0 : nat) (x1 : nat) := int_of_num (Nat.add x0 x1).
Definition term406 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : int) := ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ ((@IN a0 x0 x1) /\ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)))).
Definition term363 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := fun y0 : a0 => (~ (@IN a0 y0 x0)) \/ (Peano.lt (x1 y0) (Nat.add (x1 y0) (NUMERAL (BIT1 0)))).
Definition term43 (x0 : int) (x1 : int) := ~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term133 (x0 : int) (x1 : int) := real_sub (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term183 (x0 : int) (x1 : int) := or (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))).
Definition term248 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term151 (x0 : int) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term135 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term296 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := forall y0 : a0 -> nat, ((@FINITE a0 x1) /\ ((~ (x1 = (@EMPTY a0))) /\ (forall y1 : a0, (@IN a0 y1 x1) -> Peano.lt (x0 y1) (y0 y1)))) -> Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 y0).
Definition term290 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ ((~ (y0 = (@EMPTY a0))) /\ (forall y1 : a0, (@IN a0 y1 y0) -> Peano.lt (x0 y1) (x1 y1)))) -> Peano.lt (@nsum a0 y0 x0) (@nsum a0 y0 x1).
Definition term229 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term384 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : int) := ~ ((~ (@IN a0 x0 x1)) \/ (int_lt x2 (int_add x2 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term208 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term236 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term157 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term325 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := ((@FINITE a0 x0) /\ ((~ (x0 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.lt (x1 y0) ((fun y1 : a0 => Nat.add (x1 y1) (NUMERAL (BIT1 0))) y0)))) -> Peano.lt (@nsum a0 x0 x1) (@nsum a0 x0 (fun y0 : a0 => Nat.add (x1 y0) (NUMERAL (BIT1 0)))).
Definition term107 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term68 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term258 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term428 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := Peano.le (@nsum a0 x0 (fun y0 : a0 => Nat.add (x1 y0) (NUMERAL (BIT1 0)))) x2.
Definition term114 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term274 (x0 : nat) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) -> ((int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)) /\ (int_lt (int_of_num x0) (int_of_num x1))) \/ ((~ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) /\ (~ (int_lt (int_of_num x0) (int_of_num x1)))).
Definition term126 := real_div (real_of_num (NUMERAL 0)).
Definition term350 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := Peano.lt (x0 x1) (Nat.add (x0 x1) (NUMERAL (BIT1 0))).
Definition term44 (x0 : int) (x1 : int) := ~ (int_lt x0 x1).
Definition term370 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := or (~ (@IN a0 x0 x1)).
Definition term250 := real_add (real_of_num (NUMERAL 0)).
Definition term404 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : int) := (~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x2)) /\ ((@IN a0 x0 x1) /\ (real_le (real_add (real_of_int x2) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x2)))))) -> False.
Definition term270 (x0 : int) (x1 : int) := (~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) \/ (real_le (real_of_int x1) (real_of_int x0))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))))))) -> False.
Definition term20 (x0 : nat) (x1 : nat) := ~ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1).
Definition term427 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0 -> Prop) := (@FINITE a0 x2) /\ ((~ (x2 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x2) -> Peano.le ((fun y1 : a0 => Nat.add (x0 y1) (NUMERAL (BIT1 0))) y0) (Nat.div x1 (@CARD a0 x2)))).
Definition term320 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0 -> Prop) := (@FINITE a0 x2) /\ ((~ (x2 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x2) -> Peano.lt (x0 y0) (Nat.div x1 (@CARD a0 x2)))).
Definition term282 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0 -> Prop) := (@FINITE a0 x2) /\ ((~ (x2 = (@EMPTY a0))) /\ (forall y0 : a0, (@IN a0 y0 x2) -> Peano.le (x0 y0) (Nat.div x1 (@CARD a0 x2)))).
Definition term246 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term171 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term79 := int_of_num (NUMERAL (BIT1 0)).
Definition term249 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)).
Definition term392 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term10 (x0 : nat) := int_le (int_of_num (Nat.add x0 (NUMERAL (BIT1 0)))).
Definition term6 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_of_num x1).
Definition term0 (x0 : nat) (x1 : nat) := Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1.
Definition term421 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x2) -> Peano.le ((fun y1 : a0 => Nat.add (x0 y1) (NUMERAL (BIT1 0))) y0) (Nat.div x1 (@CARD a0 x2)).
Definition term343 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (fun y0 : a0 => (fun y1 : a0 => Nat.add (x0 y1) (NUMERAL (BIT1 0))) y0) x1.
Definition term9 := NUMERAL (BIT1 0).
Definition term206 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term367 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := int_add (int_of_num (x0 x1)) (int_of_num (NUMERAL (BIT1 0))).
Definition term140 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term319 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.lt x0 y1) /\ (Peano.le y1 y0)) -> Peano.lt x0 y0) x1.
Definition term39 (x0 : int) (x1 : int) := or (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term95 (x0 : int) (x1 : int) := ((real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) \/ (real_le (real_of_int x1) (real_of_int x0))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term213 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term38 (x0 : int) (x1 : int) := or (~ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term104 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
