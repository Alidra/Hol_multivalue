Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term471 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => fun y1 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) /\ ((@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 (S x1))).
Definition term421 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ~ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) x1)).
Definition term26 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0 -> Prop, ((@FINITE a0 y1) -> Peano.le y0 (@CARD a0 y1)) = (exists y2 : a0 -> Prop, (@SUBSET a0 y2 y1) /\ (@HAS_SIZE a0 y2 y0))) x0.
Definition term226 (x0 : int) (x1 : int) := (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))).
Definition term289 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term307 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term251 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term346 (x0 : Prop) := forall y0 : Prop, (y0 -> x0) = ((~ x0) -> ~ y0).
Definition term152 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term164 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term94 (x0 : int) (x1 : int) := (~ (int_le x1 x0)) /\ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term295 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term319 (x0 : Prop) := fun y0 : Prop => (~ (y0 /\ x0)) = (y0 -> ~ x0).
Definition term323 (x0 : Prop) := True -> ~ x0.
Definition term117 (x0 : int) (x1 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_add x1 (int_of_num (NUMERAL (BIT1 0))))).
Definition term333 (x0 : Prop) := @eq Prop (~ (False /\ x0)).
Definition term207 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term175 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term515 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = (S x1)).
Definition term229 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term284 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term215 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term509 (a0 : Type') (x0 : type686 a0) (x1 : nat) := (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y1 (S x1))) y0) -> exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) /\ ((@SUBSET a0 y1 y2) /\ (@HAS_SIZE a0 y1 (S x1)))) y0.
Definition term285 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term435 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term293 (x0 : int) := real_add (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term446 (a0 : Type') (x0 : type686 a0) (x1 : nat) := exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (exists y1 : a0 -> Prop, (@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 (S x1))).
Definition term79 (x0 : int) (x1 : int) := (~ (~ (int_le x1 x0))) \/ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term151 (x0 : nat) := real_neg (real_of_num x0).
Definition term519 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@SUBSET a0 x0 x1).
Definition term110 := real_of_int (int_of_num (NUMERAL 0)).
Definition term141 (x0 : Prop) := ~ (~ x0).
Definition term111 := real_of_num (NUMERAL 0).
Definition term27 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) -> Peano.le x0 (@CARD a0 y0)) = (exists y1 : a0 -> Prop, (@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 x0)).
Definition term22 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, (x0 /\ (exists y1 : a0, y0 y1)) = (exists y1 : a0, x0 /\ (y0 y1)).
Definition term385 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x0).
Definition term81 (x0 : int) (x1 : int) := ~ ((~ (int_le x1 x0)) /\ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term294 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term398 (a0 : Type') (x0 : nat) := ((forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) /\ (@IN (a0 -> Prop) y1 (@EMPTY (a0 -> Prop)))) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0)) /\ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x0))) -> True.
Definition term6 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (@SUBSET a0 x1 y0).
Definition term104 (x0 : int) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> ((~ (int_le x1 x0)) /\ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) \/ ((int_le x1 x0) /\ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)))).
Definition term48 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) /\ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1).
Definition term51 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (~ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1)).
Definition term36 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (~ (Peano.le (S x0) x1)).
Definition term392 (a0 : Type') (x0 : type686 a0) := @CARD a0 (@UNIONS a0 x0).
Definition term223 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term321 (x0 : Prop) := (fun y0 : Prop => (~ (y0 /\ x0)) = (y0 -> ~ x0)) True.
Definition term352 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 -> x0) = ((~ x0) -> ~ y0)) x1.
Definition term108 := int_of_num (NUMERAL 0).
Definition term63 (x0 : nat) := int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))).
Definition term313 (x0 : int) (x1 : int) := ((~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_of_int x1) (real_of_int x0)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))))))) -> False) -> ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_of_int x1) (real_of_int x0)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))))).
Definition term66 (x0 : nat) (x1 : nat) := or ((~ (int_le (int_of_num x1) (int_of_num x0))) /\ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))).
Definition term473 (a0 : Type') (x0 : type686 a0) (x1 : nat) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => fun y1 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) /\ ((@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 (S x1)))) x2 x3.
Definition term283 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term213 := ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term287 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term217 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term504 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y1 (S x1))) y0.
Definition term455 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 (S x1))) y0.
Definition term410 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (@IN (a0 -> Prop) y1 x0) -> (@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) x1)) y0.
Definition term227 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term177 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x0) (real_of_int x1)).
Definition term540 (a0 : Type') (x0 : type686 a0) := (~ (x0 = (@EMPTY (a0 -> Prop)))) /\ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 x0) /\ (@IN (a0 -> Prop) y1 x0)) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0)).
Definition term538 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term201 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term452 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 -> Prop => (@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 (S x1)).
Definition term361 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@IN (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))) /\ (@IN (a0 -> Prop) x1 (@EMPTY (a0 -> Prop))).
Definition term303 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term454 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := (@SUBSET a0 x1 x0) /\ (@HAS_SIZE a0 x1 (S x2)).
Definition term476 (a0 : Type') (x0 : type686 a0) (x1 : nat) (x2 : a0 -> Prop) := exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => fun y2 : a0 -> Prop => (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y2 y1) /\ (@HAS_SIZE a0 y2 (S x1)))) x2 y0.
Definition term84 (x0 : int) (x1 : int) := ~ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term73 (x0 : int) (x1 : int) := ~ (~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> ((~ (int_le x1 x0)) /\ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) \/ ((int_le x1 x0) /\ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))))).
Definition term241 (x0 : int) (x1 : int) := (real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))))).
Definition term159 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term345 (x0 : Prop) := forall y0 : Prop, ((~ x0) -> ~ y0) = (y0 -> x0).
Definition term347 := fun y0 : Prop => forall y1 : Prop, ((~ y0) -> ~ y1) = (y1 -> y0).
Definition term187 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term25 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term98 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ (((int_le x1 x0) \/ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))) /\ ((~ (int_le x1 x0)) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term499 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => ((@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))) -> exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y0 y1) /\ (@HAS_SIZE a0 y0 (S x1))).
Definition term507 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) /\ ((@SUBSET a0 y1 y2) /\ (@HAS_SIZE a0 y1 (S x1)))) y0.
Definition term49 (x0 : nat) (x1 : nat) := or ((~ (Peano.le x1 x0)) /\ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1)).
Definition term37 (x0 : nat) (x1 : nat) := or ((~ (Peano.le x1 x0)) /\ (Peano.le (S x0) x1)).
Definition term514 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @HAS_SIZE a0 x0 (S x1).
Definition term501 (a0 : Type') (x0 : type686 a0) (x1 : nat) := forall y0 : a0 -> Prop, ((@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))) -> exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y0 y1) /\ (@HAS_SIZE a0 y0 (S x1))).
Definition term2 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@SUBSET a0 y0 (@UNIONS a0 x0)) /\ ((~ (x0 = (@EMPTY (a0 -> Prop)))) /\ (forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@IN (a0 -> Prop) y1 x0) /\ (@IN (a0 -> Prop) y2 x0)) -> (@SUBSET a0 y1 y2) \/ (@SUBSET a0 y2 y1))))) -> exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ (@SUBSET a0 y0 y1).
Definition term97 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ (~ (((~ (int_le x1 x0)) /\ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) \/ ((int_le x1 x0) /\ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))))).
Definition term276 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term335 (x0 : Prop) := forall y0 : Prop, (~ (x0 -> y0)) = (x0 /\ (~ y0)).
Definition term67 (x0 : nat) (x1 : nat) := and (int_le (int_of_num x0) (int_of_num x1)).
Definition term120 (x0 : int) := real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term99 (x0 : int) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x1) -> ((~ (int_le x1 x0)) /\ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) \/ ((int_le x1 x0) /\ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)))).
Definition term140 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_of_int x1) (real_of_int x0)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))))).
Definition term173 (x0 : int) := real_ge (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term380 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := (@IN (a0 -> Prop) x1 x0) -> (@FINITE a0 x1) /\ (Peano.le (@CARD a0 x1) x2).
Definition term7 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (forall y0 : type686 a0, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y1 (@UNIONS a0 y0)) /\ ((~ (y0 = (@EMPTY (a0 -> Prop)))) /\ (forall y2 : a0 -> Prop, forall y3 : a0 -> Prop, ((@IN (a0 -> Prop) y2 y0) /\ (@IN (a0 -> Prop) y3 y0)) -> (@SUBSET a0 y2 y3) \/ (@SUBSET a0 y3 y2))))) -> exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y0) /\ (@SUBSET a0 y1 y2)) -> exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (@SUBSET a0 x1 y0).
Definition term326 (x0 : Prop) (x1 : Prop) := x0 -> ~ x1.
Definition term224 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term230 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term216 (x0 : nat) := real_add (real_of_num x0) (real_neg (real_of_num x0)).
Definition term534 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@IN (a0 -> Prop) x1 x0) /\ (@IN (a0 -> Prop) y0 x0)) -> (@SUBSET a0 x1 y0) \/ (@SUBSET a0 y0 x1)) x2.
Definition term265 (x0 : int) (x1 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term513 (a0 : Type') (x0 : type686 a0) (x1 : nat) := @eq Prop ((forall y0 : a0 -> Prop, ((@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))) -> exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y0 y1) /\ (@HAS_SIZE a0 y0 (S x1)))) -> (exists y0 : a0 -> Prop, (@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))) -> exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y0 y1) /\ (@HAS_SIZE a0 y0 (S x1)))).
Definition term448 (a0 : Type') (x0 : Prop) (x1 : type686 a0) := x0 /\ (exists y0 : a0 -> Prop, x1 y0).
Definition term477 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, (fun y2 : a0 -> Prop => fun y3 : a0 -> Prop => (@IN (a0 -> Prop) y2 x0) /\ ((@SUBSET a0 y3 y2) /\ (@HAS_SIZE a0 y3 (S x1)))) y0 y1.
Definition term495 (a0 : Type') (x0 : type686 a0) (x1 : nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y0 y1) /\ (@HAS_SIZE a0 y0 (S x1)))) x2.
Definition term511 (a0 : Type') (x0 : type686 a0) (x1 : nat) := (fun y0 : Prop => (forall y1 : a0 -> Prop, ((@SUBSET a0 y1 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y1 (S x1))) -> exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) /\ ((@SUBSET a0 y1 y2) /\ (@HAS_SIZE a0 y1 (S x1)))) -> y0) ((exists y0 : a0 -> Prop, (@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))) -> exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y0 y1) /\ (@HAS_SIZE a0 y0 (S x1)))).
Definition term308 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term54 (x0 : nat) (x1 : nat) := ~ (int_le (int_of_num x0) (int_of_num x1)).
Definition term281 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term280 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term211 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term206 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term437 (a0 : Type') (x0 : type686 a0) (x1 : nat) (x2 : a0 -> Prop) := (@IN (a0 -> Prop) x2 x0) /\ ((@FINITE a0 x2) -> Peano.le (S x1) (@CARD a0 x2)).
Definition term320 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (~ (y0 /\ x0)) = (y0 -> ~ x0)) x1.
Definition term184 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term470 (a0 : Type') (x0 : type686 a0) (x1 : nat) := exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, (fun y2 : a0 -> Prop => fun y3 : a0 -> Prop => (@IN (a0 -> Prop) y2 x0) /\ ((@SUBSET a0 y3 y2) /\ (@HAS_SIZE a0 y3 (S x1)))) y1 y0.
Definition term469 (a0 : Type') (x0 : type686 a0) (x1 : nat) := exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, (fun y2 : a0 -> Prop => fun y3 : a0 -> Prop => (@IN (a0 -> Prop) y2 x0) /\ ((@SUBSET a0 y3 y2) /\ (@HAS_SIZE a0 y3 (S x1)))) y0 y1.
Definition term468 (a0 : Type') (x0 : type639 a0) := exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, x0 y1 y0.
Definition term467 (a0 : Type') (x0 : type639 a0) := exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, x0 y0 y1.
Definition term539 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term198 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term150 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term270 (x0 : int) (x1 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))) (real_of_num (NUMERAL 0)).
Definition term114 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term378 (a0 : Type') (x0 : a0 -> Prop) := imp (@IN (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))).
Definition term531 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) /\ (@SUBSET a0 x1 y0).
Definition term176 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term8 (a0 : Type') := (forall y0 : type686 a0, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y1 (@UNIONS a0 y0)) /\ ((~ (y0 = (@EMPTY (a0 -> Prop)))) /\ (forall y2 : a0 -> Prop, forall y3 : a0 -> Prop, ((@IN (a0 -> Prop) y2 y0) /\ (@IN (a0 -> Prop) y3 y0)) -> (@SUBSET a0 y2 y3) \/ (@SUBSET a0 y3 y2))))) -> exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y0) /\ (@SUBSET a0 y1 y2)) -> forall y0 : type686 a0, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y1 (@UNIONS a0 y0)) /\ ((~ (y0 = (@EMPTY (a0 -> Prop)))) /\ (forall y2 : a0 -> Prop, forall y3 : a0 -> Prop, ((@IN (a0 -> Prop) y2 y0) /\ (@IN (a0 -> Prop) y3 y0)) -> (@SUBSET a0 y2 y3) \/ (@SUBSET a0 y3 y2))))) -> exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y0) /\ (@SUBSET a0 y1 y2).
Definition term172 (x0 : int) := real_ge (real_of_int x0).
Definition term24 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term450 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := (@IN (a0 -> Prop) x1 x0) /\ (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 (S x2))) y0).
Definition term356 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term182 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term93 (x0 : int) (x1 : int) := ~ (((~ (int_le x1 x0)) /\ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) \/ ((int_le x1 x0) /\ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)))).
Definition term459 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0 -> Prop) := (@IN (a0 -> Prop) x1 x0) /\ ((fun y0 : a0 -> Prop => (@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 (S x2))) x3).
Definition term132 (x0 : int) (x1 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x1).
Definition term19 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term28 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) -> Peano.le x0 (@CARD a0 y0)) = (exists y1 : a0 -> Prop, (@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 x0))) x1.
Definition term23 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 /\ (exists y1 : a0, y0 y1)) = (exists y1 : a0, x0 /\ (y0 y1))) x1.
Definition term523 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ ((@SUBSET a0 x1 y0) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = (S x2)))).
Definition term483 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ ((@SUBSET a0 x1 y0) /\ (@HAS_SIZE a0 x1 (S x2))).
Definition term463 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : a0 -> Prop, (@IN (a0 -> Prop) x1 x0) /\ ((@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 (S x2))).
Definition term439 (a0 : Type') (x0 : type686 a0) (x1 : nat) := exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ ((@FINITE a0 y0) -> Peano.le (S x1) (@CARD a0 y0)).
Definition term191 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term82 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term264 (x0 : int) (x1 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term259 (x0 : int) (x1 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))) (real_of_num (NUMERAL 0)).
Definition term154 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term129 (x0 : int) (x1 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term236 (x0 : int) (x1 : int) := ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term242 (x0 : int) (x1 : int) := ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))))).
Definition term301 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term331 (x0 : Prop) := @eq Prop (~ (True /\ x0)).
Definition term90 (x0 : int) (x1 : int) := and ((int_le x1 x0) \/ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term103 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (((int_le x1 x0) \/ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))) /\ ((~ (int_le x1 x0)) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)))).
Definition term387 (a0 : Type') (x0 : nat) := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) /\ (@IN (a0 -> Prop) y1 (@EMPTY (a0 -> Prop)))) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0)) /\ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x0)).
Definition term386 (a0 : Type') (x0 : type686 a0) (x1 : nat) := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 x0) /\ (@IN (a0 -> Prop) y1 x0)) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0)) /\ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x1)).
Definition term194 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term171 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term209 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term372 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) /\ (@IN (a0 -> Prop) y1 (@EMPTY (a0 -> Prop)))) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0).
Definition term371 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 x0) /\ (@IN (a0 -> Prop) y1 x0)) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0).
Definition term502 (a0 : Type') (x0 : type686 a0) (x1 : nat) := imp (forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y1 (S x1))) y0) -> (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) /\ ((@SUBSET a0 y1 y2) /\ (@HAS_SIZE a0 y1 (S x1)))) y0).
Definition term351 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (y1 -> y0) = ((~ y0) -> ~ y1)) x0.
Definition term334 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (~ (y0 -> y1)) = (y0 /\ (~ y1))) x0.
Definition term121 (x0 : int) := real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term527 (a0 : Type') (x0 : a0 -> Prop) := @eq nat (@CARD a0 x0).
Definition term166 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term325 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term302 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term237 (x0 : int) := and (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term424 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := (@IN (a0 -> Prop) x1 x0) /\ ((@FINITE a0 x1) -> ~ (Peano.le (@CARD a0 x1) x2)).
Definition term133 (x0 : int) (x1 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1).
Definition term3 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ ((@SUBSET a0 y0 (@UNIONS a0 x0)) /\ ((~ (x0 = (@EMPTY (a0 -> Prop)))) /\ (forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@IN (a0 -> Prop) y1 x0) /\ (@IN (a0 -> Prop) y2 x0)) -> (@SUBSET a0 y1 y2) \/ (@SUBSET a0 y2 y1))))) -> exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ (@SUBSET a0 y0 y1)) x1.
Definition term158 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term306 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term144 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_of_int x1) (real_of_int x0)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))))) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term228 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term35 (x0 : nat) (x1 : nat) := (~ (~ (Peano.le x1 x0))) /\ (~ (Peano.le (S x0) x1)).
Definition term474 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IN (a0 -> Prop) x1 x0) /\ ((@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 (S x2)))) x3.
Definition term92 (x0 : int) (x1 : int) := ((int_le x1 x0) \/ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))) /\ ((~ (int_le x1 x0)) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term441 (a0 : Type') (x0 : type686 a0) (x1 : nat) := exists y0 : a0 -> Prop, (@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1)).
Definition term247 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))))).
Definition term239 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))))).
Definition term282 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term212 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term315 (x0 : nat) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x0)) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) -> ((~ (int_le (int_of_num x1) (int_of_num x0))) /\ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ ((int_le (int_of_num x1) (int_of_num x0)) /\ (~ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)))).
Definition term279 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term431 (a0 : Type') (x0 : nat) (x1 : type686 a0) := (@FINITE a0 (@UNIONS a0 x1)) -> Peano.le (S x0) (@CARD a0 (@UNIONS a0 x1)).
Definition term178 (x0 : int) (x1 : int) := real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term340 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0, x0 y0).
Definition term425 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) /\ ((@FINITE a0 y0) -> ~ (Peano.le (@CARD a0 y0) x1)).
Definition term170 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term533 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 x0) /\ (@IN (a0 -> Prop) y1 x0)) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0)) x1.
Definition term348 := fun y0 : Prop => forall y1 : Prop, (y1 -> y0) = ((~ y0) -> ~ y1).
Definition term85 (x0 : int) (x1 : int) := or (~ (int_le x0 x1)).
Definition term174 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL 0)).
Definition term496 (a0 : Type') (x0 : type686 a0) (x1 : nat) (x2 : a0 -> Prop) := ((fun y0 : a0 -> Prop => (@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))) x2) -> (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y0 y1) /\ (@HAS_SIZE a0 y0 (S x1)))) x2.
Definition term113 := real_le (real_of_num (NUMERAL 0)).
Definition term118 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term309 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term21 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0 -> Prop, (y0 /\ (exists y2 : a0, y1 y2)) = (exists y2 : a0, y0 /\ (y1 y2))) x0.
Definition term444 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := (@IN (a0 -> Prop) x1 x0) /\ (exists y0 : a0 -> Prop, (@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 (S x2))).
Definition term430 (a0 : Type') (x0 : type686 a0) := imp (@FINITE a0 (@UNIONS a0 x0)).
Definition term500 (a0 : Type') (x0 : type686 a0) (x1 : nat) := forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y1 (S x1))) y0) -> (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) /\ ((@SUBSET a0 y1 y2) /\ (@HAS_SIZE a0 y1 (S x1)))) y0.
Definition term238 (x0 : int) (x1 : int) := (real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term342 (x0 : Prop) (x1 : Prop) := (~ x0) -> ~ x1.
Definition term512 (a0 : Type') (x0 : type686 a0) (x1 : nat) := @eq Prop ((fun y0 : Prop => (forall y1 : a0 -> Prop, ((@SUBSET a0 y1 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y1 (S x1))) -> exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) /\ ((@SUBSET a0 y1 y2) /\ (@HAS_SIZE a0 y1 (S x1)))) -> y0) ((exists y0 : a0 -> Prop, (@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))) -> exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y0 y1) /\ (@HAS_SIZE a0 y0 (S x1))))).
Definition term427 (a0 : Type') (x0 : type686 a0) (x1 : nat) := ((@FINITE a0 (@UNIONS a0 x0)) -> ~ (Peano.le (@CARD a0 (@UNIONS a0 x0)) x1)) -> exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ ((@FINITE a0 y0) -> ~ (Peano.le (@CARD a0 y0) x1)).
Definition term249 := real_lt (real_of_num (NUMERAL 0)).
Definition term422 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) -> ~ (Peano.le (@CARD a0 x0) x1).
Definition term179 (x0 : int) (x1 : int) := real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)).
Definition term125 (x0 : int) := real_add (real_of_int x0).
Definition term71 (x0 : nat) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) x0.
Definition term70 (x0 : nat) (x1 : nat) := ((~ (int_le (int_of_num x1) (int_of_num x0))) /\ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ ((int_le (int_of_num x1) (int_of_num x0)) /\ (~ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)))).
Definition term364 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x1 x0) \/ (@SUBSET a0 x0 x1).
Definition term526 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term142 (x0 : int) (x1 : int) := ~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_of_int x1) (real_of_int x0)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))))))).
Definition term101 (x0 : int) (x1 : int) := ((~ (int_le x1 x0)) /\ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) \/ ((int_le x1 x0) /\ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term52 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) /\ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1)) \/ ((Peano.le x1 x0) /\ (~ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1))).
Definition term39 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) /\ (Peano.le (S x0) x1)) \/ ((Peano.le x1 x0) /\ (~ (Peano.le (S x0) x1))).
Definition term91 (x0 : int) (x1 : int) := (~ ((~ (int_le x1 x0)) /\ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))) /\ (~ ((int_le x1 x0) /\ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)))).
Definition term262 (x0 : int) (x1 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term256 (x0 : int) (x1 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))).
Definition term234 (x0 : int) (x1 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term131 (x0 : int) (x1 : int) := (real_le (real_of_int x0) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term339 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, y0 y1)) = (exists y1 : a0, ~ (y0 y1))) x0.
Definition term453 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 (S x1))) x2.
Definition term311 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term517 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := (@SUBSET a0 x1 (@UNIONS a0 x0)) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = (S x2))).
Definition term491 (a0 : Type') (x0 : type686 a0) (x1 : nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))) x2.
Definition term367 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@IN (a0 -> Prop) x1 x0) /\ (@IN (a0 -> Prop) y0 x0)) -> (@SUBSET a0 x1 y0) \/ (@SUBSET a0 y0 x1).
Definition term40 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term275 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term109 (x0 : nat) := real_of_int (int_of_num x0).
Definition term220 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term492 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := (@SUBSET a0 x1 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 x1 (S x2)).
Definition term286 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term165 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term83 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term412 (a0 : Type') (x0 : type686 a0) (x1 : nat) := ~ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x1)).
Definition term119 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term405 (a0 : Type') (x0 : type686 a0) := ~ (forall y0 : a0 -> Prop, x0 y0).
Definition term493 (a0 : Type') (x0 : type686 a0) (x1 : nat) (x2 : a0 -> Prop) := imp ((fun y0 : a0 -> Prop => (@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))) x2).
Definition term277 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term363 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp ((@IN (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))) /\ (@IN (a0 -> Prop) x1 (@EMPTY (a0 -> Prop)))).
Definition term157 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term145 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_of_int x1) (real_of_int x0)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))))) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))).
Definition term69 (x0 : nat) (x1 : nat) := (int_le (int_of_num x1) (int_of_num x0)) /\ (~ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))).
Definition term310 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term192 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term408 (a0 : Type') (x0 : type686 a0) (x1 : nat) := exists y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => (@IN (a0 -> Prop) y1 x0) -> (@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) x1)) y0).
Definition term95 (x0 : int) (x1 : int) := (int_le x1 x0) /\ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term246 (x0 : int) (x1 : int) := (real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term208 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1.
Definition term389 (a0 : Type') (x0 : nat) := imp ((forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) /\ (@IN (a0 -> Prop) y1 (@EMPTY (a0 -> Prop)))) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0)) /\ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x0))).
Definition term388 (a0 : Type') (x0 : type686 a0) (x1 : nat) := imp ((forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 x0) /\ (@IN (a0 -> Prop) y1 x0)) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0)) /\ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x1))).
Definition term376 (a0 : Type') := and (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) /\ (@IN (a0 -> Prop) y1 (@EMPTY (a0 -> Prop)))) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0)).
Definition term375 (a0 : Type') (x0 : type686 a0) := and (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 x0) /\ (@IN (a0 -> Prop) y1 x0)) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0)).
Definition term200 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term115 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) (int_add x1 (int_of_num (NUMERAL (BIT1 0)))).
Definition term274 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0).
Definition term409 (a0 : Type') (x0 : type686 a0) (x1 : nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x1)) x2.
Definition term332 (x0 : Prop) := @eq Prop (~ x0).
Definition term341 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term525 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @SUBSET a0 x0 (@UNIONS a0 x1).
Definition term535 (a0 : Type') (x0 : type686 a0) := and (~ (x0 = (@EMPTY (a0 -> Prop)))).
Definition term521 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : nat) := (@IN (a0 -> Prop) x1 x0) /\ ((@SUBSET a0 x2 x1) /\ ((@FINITE a0 x2) /\ ((@CARD a0 x2) = (S x3)))).
Definition term353 (a0 : Type') (x0 : type686 a0) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (@EMPTY (a0 -> Prop))).
Definition term296 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term438 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) /\ ((@FINITE a0 y0) -> Peano.le (S x1) (@CARD a0 y0)).
Definition term411 (a0 : Type') (x0 : type686 a0) (x1 : nat) := forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (@IN (a0 -> Prop) y1 x0) -> (@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) x1)) y0.
Definition term128 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term417 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => (@IN (a0 -> Prop) y1 x0) -> (@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) x1)) y0).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := (@FINITE a0 x0) /\ ((@SUBSET a0 x0 (@UNIONS a0 x1)) /\ ((~ (x1 = (@EMPTY (a0 -> Prop)))) /\ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 x1) /\ (@IN (a0 -> Prop) y1 x1)) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0)))).
Definition term402 (a0 : Type') (x0 : type686 a0) (x1 : nat) := (@FINITE a0 (@UNIONS a0 x0)) -> ~ (Peano.le (@CARD a0 (@UNIONS a0 x0)) x1).
Definition term443 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := exists y0 : a0 -> Prop, (@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 (S x1)).
Definition term189 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term362 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : type686 a0) := imp ((@IN (a0 -> Prop) x0 x2) /\ (@IN (a0 -> Prop) x1 x2)).
Definition term384 (a0 : Type') (x0 : type686 a0) (x1 : nat) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x1).
Definition term180 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term327 (x0 : Prop) (x1 : Prop) := @eq Prop ((~ (x0 /\ x1)) = (x0 -> ~ x1)).
Definition term358 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := and (@IN (a0 -> Prop) x0 x1).
Definition term268 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term257 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term87 (x0 : int) (x1 : int) := (~ (int_le x1 x0)) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term400 (a0 : Type') (x0 : type686 a0) (x1 : nat) := (~ ((@FINITE a0 (@UNIONS a0 x0)) /\ (Peano.le (@CARD a0 (@UNIONS a0 x0)) x1))) -> ~ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x1)).
Definition term355 (a0 : Type') (x0 : type686 a0) := ~ (x0 = (@EMPTY (a0 -> Prop))).
Definition term193 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term64 (x0 : nat) (x1 : nat) := int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1).
Definition term429 (a0 : Type') (x0 : nat) (x1 : type686 a0) := Peano.le (S x0) (@CARD a0 (@UNIONS a0 x1)).
Definition term135 (x0 : int) (x1 : int) := (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term273 (x0 : int) := real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term261 (x0 : int) (x1 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))).
Definition term418 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => ~ ((@IN (a0 -> Prop) y0 x0) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x1)).
Definition term516 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := and (@SUBSET a0 x0 (@UNIONS a0 x1)).
Definition term162 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term299 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term377 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := imp (@IN (a0 -> Prop) x0 x1).
Definition term42 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term232 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0.
Definition term253 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term305 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term357 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term329 (x0 : Prop) := ~ (False /\ x0).
Definition term116 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term498 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y1 (S x1))) y0) -> (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) /\ ((@SUBSET a0 y1 y2) /\ (@HAS_SIZE a0 y1 (S x1)))) y0.
Definition term506 (a0 : Type') (x0 : type686 a0) (x1 : nat) := imp (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y1 (S x1))) y0).
Definition term210 := S (Nat.add 0 0).
Definition term155 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term197 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term231 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term324 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (~ (y0 /\ x0)) = (y0 -> ~ x0)) x1).
Definition term153 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term518 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := imp ((@SUBSET a0 x1 (@UNIONS a0 x0)) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = (S x2)))).
Definition term415 (a0 : Type') (x0 : type686 a0) (x1 : nat) (x2 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x1)) x2).
Definition term245 (x0 : int) (x1 : int) := ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))))) \/ ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))))).
Definition term186 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term416 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := ~ ((@IN (a0 -> Prop) x1 x0) -> (@FINITE a0 x1) /\ (Peano.le (@CARD a0 x1) x2)).
Definition term403 (a0 : Type') (x0 : type686 a0) (x1 : nat) := imp (~ ((@FINITE a0 (@UNIONS a0 x0)) /\ (Peano.le (@CARD a0 (@UNIONS a0 x0)) x1))).
Definition term382 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x1).
Definition term426 (a0 : Type') (x0 : type686 a0) (x1 : nat) := exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ ((@FINITE a0 y0) -> ~ (Peano.le (@CARD a0 y0) x1)).
Definition term401 (a0 : Type') (x0 : type686 a0) (x1 : nat) := ~ ((@FINITE a0 (@UNIONS a0 x0)) /\ (Peano.le (@CARD a0 (@UNIONS a0 x0)) x1)).
Definition term536 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term60 (x0 : nat) := int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0))).
Definition term267 (x0 : int) (x1 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))).
Definition term243 (x0 : int) (x1 : int) := (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term481 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) /\ ((@SUBSET a0 x1 y0) /\ (@HAS_SIZE a0 x1 (S x2))).
Definition term462 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) x1 x0) /\ ((@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 (S x2))).
Definition term318 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term266 (x0 : int) (x1 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))).
Definition term218 := real_mul (real_of_num (NUMERAL 0)).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term203 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term350 := forall y0 : Prop, forall y1 : Prop, (y1 -> y0) = ((~ y0) -> ~ y1).
Definition term349 := forall y0 : Prop, forall y1 : Prop, ((~ y0) -> ~ y1) = (y1 -> y0).
Definition term461 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) x1 x0) /\ ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 (S x2))) y0).
Definition term1 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y1 (@UNIONS a0 y0)) /\ ((~ (y0 = (@EMPTY (a0 -> Prop)))) /\ (forall y2 : a0 -> Prop, forall y3 : a0 -> Prop, ((@IN (a0 -> Prop) y2 y0) /\ (@IN (a0 -> Prop) y3 y0)) -> (@SUBSET a0 y2 y3) \/ (@SUBSET a0 y3 y2))))) -> exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y0) /\ (@SUBSET a0 y1 y2)) x0.
Definition term33 (x0 : nat) (x1 : nat) := and (~ (~ (Peano.le x0 x1))).
Definition term330 (x0 : Prop) := False -> ~ x0.
Definition term127 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term374 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) /\ (@IN (a0 -> Prop) y1 (@EMPTY (a0 -> Prop)))) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0).
Definition term373 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 x0) /\ (@IN (a0 -> Prop) y1 x0)) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0).
Definition term484 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, (fun y2 : a0 -> Prop => fun y3 : a0 -> Prop => (@IN (a0 -> Prop) y2 x0) /\ ((@SUBSET a0 y3 y2) /\ (@HAS_SIZE a0 y3 (S x1)))) y1 y0.
Definition term406 (a0 : Type') (x0 : type686 a0) := exists y0 : a0 -> Prop, ~ (x0 y0).
Definition term260 (x0 : int) (x1 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term336 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (~ (x0 -> y0)) = (x0 /\ (~ y0))) x1.
Definition term72 (x0 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term160 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term503 (a0 : Type') (x0 : type686 a0) (x1 : nat) := imp (forall y0 : a0 -> Prop, ((@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))) -> exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y0 y1) /\ (@HAS_SIZE a0 y0 (S x1)))).
Definition term78 (x0 : int) (x1 : int) := or (int_le x0 x1).
Definition term222 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term528 (x0 : nat) := @eq nat (S x0).
Definition term520 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := (@SUBSET a0 x1 x0) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = (S x2))).
Definition term185 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term433 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ~ (Peano.le (@CARD a0 x0) x1).
Definition term32 (x0 : nat) (x1 : nat) := ~ (Peano.le (S x0) x1).
Definition term395 (a0 : Type') (x0 : type686 a0) (x1 : nat) := Peano.le (@CARD a0 (@UNIONS a0 x0)) x1.
Definition term487 (a0 : Type') (x0 : type686 a0) (x1 : nat) := (exists y0 : a0 -> Prop, (@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))) -> exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y0 y1) /\ (@HAS_SIZE a0 y0 (S x1))).
Definition term466 (a0 : Type') (x0 : type686 a0) (x1 : nat) := (exists y0 : a0 -> Prop, (@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))) -> exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ ((@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 (S x1))).
Definition term269 (x0 : int) (x1 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))) (real_of_num (NUMERAL 0)).
Definition term263 (x0 : int) (x1 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term258 (x0 : int) (x1 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))) (real_of_num (NUMERAL 0)).
Definition term96 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term235 (x0 : int) (x1 : int) := and ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) \/ (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)))).
Definition term543 (a0 : Type') := forall y0 : type686 a0, forall y1 : nat, ((forall y2 : a0 -> Prop, forall y3 : a0 -> Prop, ((@IN (a0 -> Prop) y2 y0) /\ (@IN (a0 -> Prop) y3 y0)) -> (@SUBSET a0 y2 y3) \/ (@SUBSET a0 y3 y2)) /\ (forall y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y0) -> (@FINITE a0 y2) /\ (Peano.le (@CARD a0 y2) y1))) -> (@FINITE a0 (@UNIONS a0 y0)) /\ (Peano.le (@CARD a0 (@UNIONS a0 y0)) y1).
Definition term0 (a0 : Type') := forall y0 : type686 a0, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y1 (@UNIONS a0 y0)) /\ ((~ (y0 = (@EMPTY (a0 -> Prop)))) /\ (forall y2 : a0 -> Prop, forall y3 : a0 -> Prop, ((@IN (a0 -> Prop) y2 y0) /\ (@IN (a0 -> Prop) y3 y0)) -> (@SUBSET a0 y2 y3) \/ (@SUBSET a0 y3 y2))))) -> exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 y0) /\ (@SUBSET a0 y1 y2).
Definition term419 (a0 : Type') (x0 : type686 a0) (x1 : nat) := exists y0 : a0 -> Prop, ~ ((@IN (a0 -> Prop) y0 x0) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x1)).
Definition term272 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_add (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term47 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) /\ (Peano.le (S x0) x1).
Definition term139 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_of_int x1) (real_of_int x0)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))).
Definition term56 (x0 : nat) (x1 : nat) := int_le (int_of_num (Nat.add x0 (NUMERAL (BIT1 0)))) (int_of_num x1).
Definition term190 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term147 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term106 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term298 (x0 : int) (x1 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))).
Definition term233 (x0 : int) (x1 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term414 (a0 : Type') (x0 : type686 a0) (x1 : nat) := @eq Prop (~ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x1))).
Definition term413 (a0 : Type') (x0 : type686 a0) (x1 : nat) := @eq Prop (~ (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (@IN (a0 -> Prop) y1 x0) -> (@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) x1)) y0)).
Definition term428 (a0 : Type') (x0 : type686 a0) (x1 : nat) := ~ (Peano.le (@CARD a0 (@UNIONS a0 x0)) x1).
Definition term102 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (~ ((int_le (int_of_num (NUMERAL 0)) x1) -> ((~ (int_le x1 x0)) /\ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) \/ ((int_le x1 x0) /\ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))))).
Definition term497 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := ((@SUBSET a0 x1 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 x1 (S x2))) -> exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ ((@SUBSET a0 x1 y0) /\ (@HAS_SIZE a0 x1 (S x2))).
Definition term31 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term508 (a0 : Type') (x0 : type686 a0) (x1 : nat) := exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) /\ ((@SUBSET a0 y1 y2) /\ (@HAS_SIZE a0 y1 (S x1)))) y0.
Definition term89 (x0 : int) (x1 : int) := and (~ ((~ (int_le x1 x0)) /\ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term542 (a0 : Type') (x0 : type686 a0) := forall y0 : nat, ((forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@IN (a0 -> Prop) y1 x0) /\ (@IN (a0 -> Prop) y2 x0)) -> (@SUBSET a0 y1 y2) \/ (@SUBSET a0 y2 y1)) /\ (forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) -> (@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y0))) -> (@FINITE a0 (@UNIONS a0 x0)) /\ (Peano.le (@CARD a0 (@UNIONS a0 x0)) y0).
Definition term167 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term449 (a0 : Type') (x0 : Prop) (x1 : type686 a0) := exists y0 : a0 -> Prop, x0 /\ (x1 y0).
Definition term55 (x0 : nat) (x1 : nat) := and (~ (int_le (int_of_num x0) (int_of_num x1))).
Definition term148 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := exists y0 : a0 -> Prop, (@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 x1).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term328 (x0 : Prop) := (fun y0 : Prop => (~ (y0 /\ x0)) = (y0 -> ~ x0)) False.
Definition term343 (x0 : Prop) := fun y0 : Prop => ((~ x0) -> ~ y0) = (y0 -> x0).
Definition term163 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term530 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN (a0 -> Prop) x2 x0) /\ (@SUBSET a0 x1 x2).
Definition term479 (a0 : Type') (x0 : type686 a0) (x1 : nat) := @eq Prop (exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ ((@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 (S x1)))).
Definition term478 (a0 : Type') (x0 : type686 a0) (x1 : nat) := @eq Prop (exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, (fun y2 : a0 -> Prop => fun y3 : a0 -> Prop => (@IN (a0 -> Prop) y2 x0) /\ ((@SUBSET a0 y3 y2) /\ (@HAS_SIZE a0 y3 (S x1)))) y0 y1).
Definition term169 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term486 (a0 : Type') (x0 : type686 a0) (x1 : nat) := exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y0 y1) /\ (@HAS_SIZE a0 y0 (S x1))).
Definition term465 (a0 : Type') (x0 : type686 a0) (x1 : nat) := exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ ((@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 (S x1))).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term529 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x0 x1) /\ True.
Definition term458 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := @eq Prop ((@IN (a0 -> Prop) x1 x0) /\ (exists y0 : a0 -> Prop, (@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 (S x2)))).
Definition term457 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := @eq Prop ((@IN (a0 -> Prop) x1 x0) /\ (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 (S x2))) y0)).
Definition term88 (x0 : int) (x1 : int) := ~ ((int_le x1 x0) /\ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term221 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term124 := real_of_num (NUMERAL (BIT1 0)).
Definition term254 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term314 (x0 : int) (x1 : int) := ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_of_int x1) (real_of_int x0)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))))).
Definition term107 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term41 (x0 : nat) (x1 : nat) := Peano.le (S x0) x1.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0) -> (forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term297 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term86 (x0 : int) (x1 : int) := (~ (int_le x1 x0)) \/ (~ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term143 (x0 : int) (x1 : int) := ((real_le (real_of_int x1) (real_of_int x0)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))))) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term138 (x0 : int) := and (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term440 (a0 : Type') (x0 : type686 a0) (x1 : nat) := ((@FINITE a0 (@UNIONS a0 x0)) -> Peano.le (S x1) (@CARD a0 (@UNIONS a0 x0))) -> exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ ((@FINITE a0 y0) -> Peano.le (S x1) (@CARD a0 y0)).
Definition term391 (a0 : Type') (x0 : type686 a0) := and (@FINITE a0 (@UNIONS a0 x0)).
Definition term202 := real_add (real_of_num (NUMERAL (BIT1 0))).
Definition term420 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := (@IN (a0 -> Prop) x1 x0) /\ (~ ((@FINITE a0 x1) /\ (Peano.le (@CARD a0 x1) x2))).
Definition term436 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> Peano.le (S x0) (@CARD a0 x1).
Definition term381 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@IN (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))) -> (@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) x1).
Definition term204 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term74 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> ((~ (int_le x1 x0)) /\ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) \/ ((int_le x1 x0) /\ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term4 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ((@FINITE a0 x1) /\ ((@SUBSET a0 x1 (@UNIONS a0 x0)) /\ ((~ (x0 = (@EMPTY (a0 -> Prop)))) /\ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 x0) /\ (@IN (a0 -> Prop) y1 x0)) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0))))) -> exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (@SUBSET a0 x1 y0).
Definition term445 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) /\ (exists y1 : a0 -> Prop, (@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 (S x1))).
Definition term447 (a0 : Type') (x0 : type686 a0) (x1 : nat) := (exists y0 : a0 -> Prop, (@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))) -> exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (exists y1 : a0 -> Prop, (@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 (S x1))).
Definition term195 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term304 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term252 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term404 (a0 : Type') (x0 : type686 a0) (x1 : nat) := imp ((@FINITE a0 (@UNIONS a0 x0)) -> ~ (Peano.le (@CARD a0 (@UNIONS a0 x0)) x1)).
Definition term196 (x0 : int) := real_add (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term541 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := (@SUBSET a0 x0 (@UNIONS a0 x1)) /\ ((~ (x1 = (@EMPTY (a0 -> Prop)))) /\ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 x1) /\ (@IN (a0 -> Prop) y1 x1)) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0))).
Definition term240 (x0 : int) (x1 : int) := ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term532 (a0 : Type') (x0 : type686 a0) := (~ (x0 = (@EMPTY (a0 -> Prop)))) -> (x0 = (@EMPTY (a0 -> Prop))) = False.
Definition term244 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))))) \/ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)))))).
Definition term77 (x0 : int) (x1 : int) := or (~ (~ (int_le x0 x1))).
Definition term68 (x0 : nat) (x1 : nat) := ~ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)).
Definition term53 (x0 : nat) (x1 : nat) := int_le (int_of_num x0) (int_of_num x1).
Definition term123 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term316 (x0 : nat) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) -> ((~ (int_le (int_of_num x1) (int_of_num x0))) /\ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1))) \/ ((int_le (int_of_num x1) (int_of_num x0)) /\ (~ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)))).
Definition term338 (x0 : Prop) (x1 : Prop) := x0 /\ (~ x1).
Definition term161 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term18 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (exists y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a1, exists y2 : a0, y0 y2 y1)) x0.
Definition term365 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ((@IN (a0 -> Prop) x2 x0) /\ (@IN (a0 -> Prop) x1 x0)) -> (@SUBSET a0 x2 x1) \/ (@SUBSET a0 x1 x2).
Definition term394 := Peano.le (NUMERAL 0).
Definition term485 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y0 y1) /\ (@HAS_SIZE a0 y0 (S x1))).
Definition term464 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ ((@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 (S x1))).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) -> x1 y0.
Definition term134 (x0 : int) (x1 : int) := or (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term105 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> ((~ (int_le x1 x0)) /\ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)) \/ ((int_le x1 x0) /\ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term43 (x0 : nat) := Peano.le (S x0).
Definition term397 (a0 : Type') (x0 : type686 a0) (x1 : nat) := ((forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@IN (a0 -> Prop) y0 x0) /\ (@IN (a0 -> Prop) y1 x0)) -> (@SUBSET a0 y0 y1) \/ (@SUBSET a0 y1 y0)) /\ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x1))) -> (@FINITE a0 (@UNIONS a0 x0)) /\ (Peano.le (@CARD a0 (@UNIONS a0 x0)) x1).
Definition term337 (x0 : Prop) (x1 : Prop) := ~ (x0 -> x1).
Definition term59 (x0 : nat) := int_of_num (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term432 (a0 : Type') (x0 : nat) (x1 : type686 a0) := imp ((@FINITE a0 (@UNIONS a0 x1)) -> Peano.le (S x0) (@CARD a0 (@UNIONS a0 x1))).
Definition term390 (a0 : Type') (x0 : type686 a0) := @FINITE a0 (@UNIONS a0 x0).
Definition term379 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) x1).
Definition term100 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term44 (x0 : nat) := Peano.le (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term126 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term214 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term57 (x0 : nat) (x1 : nat) := int_of_num (Nat.add x0 x1).
Definition term383 (a0 : Type') (x0 : nat) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x0).
Definition term20 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a1, exists y1 : a0, x0 y1 y0.
Definition term130 (x0 : int) (x1 : int) := or (real_le (real_of_int x0) (real_of_int x1)).
Definition term76 (x0 : int) (x1 : int) := ~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term181 (x0 : int) (x1 : int) := real_sub (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term225 (x0 : int) (x1 : int) := or (real_ge (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))).
Definition term290 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term199 (x0 : int) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term359 (a0 : Type') (x0 : a0 -> Prop) := and (@IN (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))).
Definition term183 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term370 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@IN (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))) /\ (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop)))) -> (@SUBSET a0 x0 y0) \/ (@SUBSET a0 y0 x0).
Definition term369 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@IN (a0 -> Prop) x1 x0) /\ (@IN (a0 -> Prop) y0 x0)) -> (@SUBSET a0 x1 y0) \/ (@SUBSET a0 y0 x1).
Definition term480 (a0 : Type') (x0 : type686 a0) (x1 : nat) (x2 : a0 -> Prop) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => fun y2 : a0 -> Prop => (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y2 y1) /\ (@HAS_SIZE a0 y2 (S x1)))) y0 x2.
Definition term407 (a0 : Type') (x0 : type686 a0) (x1 : nat) := ~ (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (@IN (a0 -> Prop) y1 x0) -> (@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) x1)) y0).
Definition term271 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term366 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@IN (a0 -> Prop) x1 (@EMPTY (a0 -> Prop))) /\ (@IN (a0 -> Prop) x0 (@EMPTY (a0 -> Prop)))) -> (@SUBSET a0 x1 x0) \/ (@SUBSET a0 x0 x1).
Definition term136 (x0 : int) (x1 : int) := and ((real_le (real_of_int x0) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))))).
Definition term29 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> Peano.le x0 (@CARD a0 x1).
Definition term65 (x0 : nat) (x1 : nat) := (~ (int_le (int_of_num x1) (int_of_num x0))) /\ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x1)).
Definition term522 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) /\ ((@SUBSET a0 x1 y0) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = (S x2)))).
Definition term250 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term38 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) /\ (Peano.le (S x0) x1)) \/ ((~ (~ (Peano.le x1 x0))) /\ (~ (Peano.le (S x0) x1))).
Definition term278 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term205 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term460 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : nat) := (@IN (a0 -> Prop) x1 x0) /\ ((@SUBSET a0 x2 x1) /\ (@HAS_SIZE a0 x2 (S x3))).
Definition term149 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term396 (a0 : Type') (x0 : type686 a0) (x1 : nat) := (@FINITE a0 (@UNIONS a0 x0)) /\ (Peano.le (@CARD a0 (@UNIONS a0 x0)) x1).
Definition term317 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term112 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term300 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term354 (a0 : Type') (x0 : type686 a0) := (x0 = (@EMPTY (a0 -> Prop))) \/ (~ (x0 = (@EMPTY (a0 -> Prop)))).
Definition term156 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term475 (a0 : Type') (x0 : type686 a0) (x1 : nat) (x2 : a0 -> Prop) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => fun y2 : a0 -> Prop => (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y2 y1) /\ (@HAS_SIZE a0 y2 (S x1)))) x2 y0.
Definition term482 (a0 : Type') (x0 : type686 a0) (x1 : nat) (x2 : a0 -> Prop) := exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => fun y2 : a0 -> Prop => (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y2 y1) /\ (@HAS_SIZE a0 y2 (S x1)))) y0 x2.
Definition term393 (a0 : Type') (x0 : type686 a0) := Peano.le (@CARD a0 (@UNIONS a0 x0)).
Definition term423 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Peano.le (@CARD a0 x0) x1.
Definition term168 := real_div (real_of_num (NUMERAL 0)).
Definition term80 (x0 : int) (x1 : int) := (int_le x1 x0) \/ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term292 := real_add (real_of_num (NUMERAL 0)).
Definition term312 (x0 : int) (x1 : int) := (~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (((real_le (real_of_int x1) (real_of_int x0)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))))))) -> False.
Definition term524 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := ((@SUBSET a0 x1 (@UNIONS a0 x0)) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = (S x2)))) -> exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ ((@SUBSET a0 x1 y0) /\ ((@FINITE a0 x1) /\ ((@CARD a0 x1) = (S x2)))).
Definition term50 (x0 : nat) (x1 : nat) := ~ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1).
Definition term451 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : a0 -> Prop, (@IN (a0 -> Prop) x1 x0) /\ ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 x1) /\ (@HAS_SIZE a0 y1 (S x2))) y0).
Definition term510 (a0 : Type') (x0 : type686 a0) (x1 : nat) := (forall y0 : a0 -> Prop, ((@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))) -> exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y0 y1) /\ (@HAS_SIZE a0 y0 (S x1)))) -> (exists y0 : a0 -> Prop, (@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))) -> exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 x0) /\ ((@SUBSET a0 y0 y1) /\ (@HAS_SIZE a0 y0 (S x1))).
Definition term489 (a0 : Type') (x0 : type686 a0) (x1 : nat) := (forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y1 (S x1))) y0) -> (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) /\ ((@SUBSET a0 y1 y2) /\ (@HAS_SIZE a0 y1 (S x1)))) y0) -> (exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y1 (S x1))) y0) -> exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, (@IN (a0 -> Prop) y2 x0) /\ ((@SUBSET a0 y1 y2) /\ (@HAS_SIZE a0 y1 (S x1)))) y0.
Definition term488 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := (forall y0 : a0 -> Prop, (x0 y0) -> x1 y0) -> (exists y0 : a0 -> Prop, x0 y0) -> exists y0 : a0 -> Prop, x1 y0.
Definition term505 (a0 : Type') (x0 : type686 a0) (x1 : nat) := exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (@SUBSET a0 y1 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y1 (S x1))) y0.
Definition term456 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := exists y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (@SUBSET a0 y1 x0) /\ (@HAS_SIZE a0 y1 (S x1))) y0.
Definition term288 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term219 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term122 := int_of_num (NUMERAL (BIT1 0)).
Definition term360 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : type686 a0) := (@IN (a0 -> Prop) x0 x2) /\ (@IN (a0 -> Prop) x1 x2).
Definition term46 (x0 : nat) (x1 : nat) := and (~ (Peano.le x0 x1)).
Definition term291 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)).
Definition term62 (x0 : nat) := int_le (int_of_num (Nat.add x0 (NUMERAL (BIT1 0)))).
Definition term58 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_of_num x1).
Definition term75 (x0 : int) (x1 : int) := ~ (~ (int_le x0 x1)).
Definition term45 (x0 : nat) (x1 : nat) := Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x1.
Definition term34 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term61 := NUMERAL (BIT1 0).
Definition term344 (x0 : Prop) := fun y0 : Prop => (y0 -> x0) = ((~ x0) -> ~ y0).
Definition term248 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term399 (a0 : Type') (x0 : type686 a0) (x1 : nat) := (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) x1)) -> (@FINITE a0 (@UNIONS a0 x0)) /\ (Peano.le (@CARD a0 (@UNIONS a0 x0)) x1).
Definition term188 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term442 (a0 : Type') (x0 : type686 a0) (x1 : nat) := imp (exists y0 : a0 -> Prop, (@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1))).
Definition term490 (a0 : Type') (x0 : type686 a0) (x1 : nat) := fun y0 : a0 -> Prop => (@SUBSET a0 y0 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 y0 (S x1)).
Definition term368 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@IN (a0 -> Prop) x0 (@EMPTY (a0 -> Prop))) /\ (@IN (a0 -> Prop) y0 (@EMPTY (a0 -> Prop)))) -> (@SUBSET a0 x0 y0) \/ (@SUBSET a0 y0 x0).
Definition term537 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term434 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := Peano.le (S x0) (@CARD a0 x1).
Definition term472 (a0 : Type') (x0 : type686 a0) (x1 : nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => fun y1 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) /\ ((@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 (S x1)))) x2.
Definition term322 (x0 : Prop) := ~ (True /\ x0).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((forall y0 : a0, (x0 y0) -> x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0) -> (exists y0 : a0, x0 y0) -> exists y0 : a0, x1 y0.
Definition term137 (x0 : int) (x1 : int) := ((real_le (real_of_int x1) (real_of_int x0)) \/ (real_le (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))))) /\ ((real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) \/ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term255 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term494 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : nat) := imp ((@SUBSET a0 x1 (@UNIONS a0 x0)) /\ (@HAS_SIZE a0 x1 (S x2))).
Definition term146 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
