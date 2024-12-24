Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term45 (x0 : real) := forall y0 : real, ((real_sub x0 y0) = (real_of_num (NUMERAL 0))) = (x0 = y0).
Definition term178 (x0 : real) (x1 : real -> real) (x2 : real) := @SETSPEC real x0 ((x1 x2) = (real_of_num (NUMERAL 0))).
Definition term191 (x0 : nat) := (fun y0 : nat => forall y1 : nat -> real, (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((@sum nat (dotdot (NUMERAL 0) y0) (fun y4 : nat => real_mul (y1 y4) (real_pow y3 y4))) = (real_of_num (NUMERAL 0))) y3))) = (exists y2 : nat, (@IN nat y2 (dotdot (NUMERAL 0) y0)) /\ (~ ((y1 y2) = (real_of_num (NUMERAL 0)))))) x0.
Definition term161 (x0 : real -> real) := (~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1)))) -> ~ (~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0)))).
Definition term222 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (fun y0 : nat => (@IN nat y0 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y0) = (real_of_num (NUMERAL 0))))) x2.
Definition term201 (x0 : real) (x1 : nat) (x2 : nat -> real) := fun y0 : real => @SETSPEC real x0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x2 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) y0.
Definition term180 (x0 : real) (x1 : real -> real) := fun y0 : real => @SETSPEC real x0 ((x1 y0) = (real_of_num (NUMERAL 0))) y0.
Definition term117 (x0 : real) (x1 : real -> real) (x2 : real) := fun y0 : real => @SETSPEC real x0 (((fun y1 : real => real_sub (x1 y1) x2) y0) = (real_of_num (NUMERAL 0))) y0.
Definition term59 (x0 : real) (x1 : real -> real) (x2 : real) := fun y0 : real => @SETSPEC real x0 ((real_sub (x1 y0) x2) = (real_of_num (NUMERAL 0))) y0.
Definition term246 (x0 : nat -> real) (x1 : real) (x2 : nat) := (fun y0 : nat => real_mul (x0 y0) (real_pow x1 y0)) x2.
Definition term34 (x0 : Prop) := forall y0 : Prop, (y0 -> x0) = ((~ x0) -> ~ y0).
Definition term292 := fun y0 : nat => real_of_num (NUMERAL 0).
Definition term115 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real) := @SETSPEC real x0 (((fun y0 : real => real_sub (x1 y0) x2) x3) = (real_of_num (NUMERAL 0))).
Definition term199 (x0 : real) (x1 : nat) (x2 : nat -> real) (x3 : real) := @SETSPEC real x0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y0 : nat => real_mul (x2 y0) (real_pow x3 y0))) = (real_of_num (NUMERAL 0))).
Definition term270 (x0 : nat -> real) (x1 : nat) := real_mul (x0 x1).
Definition term185 := fun y0 : real => exists y1 : real, @SETSPEC real y0 True y1.
Definition term260 (x0 : nat) := @sum nat (dotdot (NUMERAL 0) x0).
Definition term17 (x0 : Prop) := ~ (~ x0).
Definition term108 (x0 : real) (x1 : real -> real) (x2 : Prop) := ((polynomial_function x1) = (polynomial_function x1)) -> ((polynomial_function x1) -> ((@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((real_sub (x1 y1) x0) = (real_of_num (NUMERAL 0))) y1))) = (~ (forall y0 : real, (real_sub (x1 y0) x0) = (real_of_num (NUMERAL 0))))) = x2) -> ((polynomial_function x1) -> (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((real_sub (x1 y1) x0) = (real_of_num (NUMERAL 0))) y1))) = (~ (forall y0 : real, (real_sub (x1 y0) x0) = (real_of_num (NUMERAL 0))))) = ((polynomial_function x1) -> x2).
Definition term2 := real_of_num (NUMERAL 0).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1))) x0.
Definition term111 (x0 : real -> real) (x1 : real) := fun y0 : real => real_sub (x0 y0) x1.
Definition term109 (x0 : real) (x1 : real -> real) (x2 : Prop) := ((polynomial_function x1) -> ((@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((real_sub (x1 y1) x0) = (real_of_num (NUMERAL 0))) y1))) = (~ (forall y0 : real, (real_sub (x1 y0) x0) = (real_of_num (NUMERAL 0))))) = x2) -> ((polynomial_function x1) -> (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((real_sub (x1 y1) x0) = (real_of_num (NUMERAL 0))) y1))) = (~ (forall y0 : real, (real_sub (x1 y0) x0) = (real_of_num (NUMERAL 0))))) = ((polynomial_function x1) -> x2).
Definition term19 (x0 : Prop) := False /\ (~ x0).
Definition term223 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (@IN nat x2 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 x2) = (real_of_num (NUMERAL 0)))).
Definition term40 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 -> x0) = ((~ x0) -> ~ y0)) x1.
Definition term80 (x0 : real -> real) := fun y0 : real => (polynomial_function x0) -> (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((real_sub (x0 y2) y0) = (real_of_num (NUMERAL 0))) y2))) = (~ (forall y1 : real, (real_sub (x0 y1) y0) = (real_of_num (NUMERAL 0)))).
Definition term79 (x0 : real -> real) := fun y0 : real => (polynomial_function x0) -> (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((x0 y2) = y0) y2))) = (~ (forall y1 : real, (x0 y1) = y0)).
Definition term297 (x0 : real -> real) := ((@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1))) -> ~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0)))) /\ ((~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0)))) -> @FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1))).
Definition term227 (x0 : nat) (x1 : nat -> real) := @eq Prop (~ (exists y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y0) = (real_of_num (NUMERAL 0)))))).
Definition term226 (x0 : nat) (x1 : nat -> real) := @eq Prop (~ (exists y0 : nat, (fun y1 : nat => (@IN nat y1 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0))))) y0)).
Definition term221 (x0 : nat) (x1 : nat -> real) := fun y0 : nat => (@IN nat y0 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y0) = (real_of_num (NUMERAL 0)))).
Definition term149 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term73 (x0 : real -> real) (x1 : real) := forall y0 : real, (real_sub (x0 y0) x1) = (real_of_num (NUMERAL 0)).
Definition term88 (x0 : real) := (fun y0 : real => polynomial_function (fun y1 : real => y0)) x0.
Definition term290 (x0 : nat -> real) (x1 : nat) := ((forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x1)) -> (x0 y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x0 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) = (forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow y0 y1))) = (real_of_num (NUMERAL 0)))) -> ((~ (exists y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x1)) /\ (~ ((x0 y0) = (real_of_num (NUMERAL 0)))))) -> forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x0 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) = ((forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x1)) -> (x0 y0) = (real_of_num (NUMERAL 0))) -> forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))).
Definition term204 (x0 : nat) (x1 : nat -> real) := @GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (x1 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1).
Definition term186 := @GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 True y1).
Definition term175 (x0 : real -> real) := @GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1).
Definition term120 (x0 : real -> real) (x1 : real) := @GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (((fun y2 : real => real_sub (x0 y2) x1) y1) = (real_of_num (NUMERAL 0))) y1).
Definition term65 (x0 : real -> real) (x1 : real) := @GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((real_sub (x0 y1) x1) = (real_of_num (NUMERAL 0))) y1).
Definition term64 (x0 : real -> real) (x1 : real) := @GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = x1) y1).
Definition term33 (x0 : Prop) := forall y0 : Prop, ((~ x0) -> ~ y0) = (y0 -> x0).
Definition term35 := fun y0 : Prop => forall y1 : Prop, ((~ y0) -> ~ y1) = (y1 -> y0).
Definition term155 (x0 : real -> real) := (exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (x0 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))) -> (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1))) = (~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0)))).
Definition term147 := fun y0 : real => True.
Definition term125 (x0 : real -> real) (x1 : real) := ~ (forall y0 : real, ((fun y1 : real => real_sub (x0 y1) x1) y0) = (real_of_num (NUMERAL 0))).
Definition term99 (x0 : real -> real) := ~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))).
Definition term75 (x0 : real -> real) (x1 : real) := ~ (forall y0 : real, (real_sub (x0 y0) x1) = (real_of_num (NUMERAL 0))).
Definition term285 (x0 : nat -> real) (x1 : nat) (x2 : real) := (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x1)) -> (real_mul (x0 y0) (real_pow x2 y0)) = (real_mul (real_of_num (NUMERAL 0)) (real_pow x2 y0))) -> (@sum nat (dotdot (NUMERAL 0) x1) (fun y0 : nat => real_mul (x0 y0) (real_pow x2 y0))) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y0 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow x2 y0))).
Definition term275 (x0 : nat -> real) (x1 : nat) (x2 : real) := (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x1)) -> (real_mul (x0 y0) (real_pow x2 y0)) = ((fun y1 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow x2 y1)) y0)) -> (@sum nat (dotdot (NUMERAL 0) x1) (fun y0 : nat => real_mul (x0 y0) (real_pow x2 y0))) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y0 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow x2 y0))).
Definition term235 (x0 : nat) (x1 : nat -> real) := fun y0 : nat => (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0)).
Definition term41 (x0 : real -> real) := (fun y0 : real -> real => (polynomial_function y0) = (exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (y0 y3) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4))))) x0.
Definition term135 (x0 : real -> real) (x1 : real) := polynomial_function (fun y0 : real => real_sub (x0 y0) ((fun y1 : real => x1) y0)).
Definition term124 (x0 : real -> real) (x1 : real) := forall y0 : real, ((fun y1 : real => real_sub (x0 y1) x1) y0) = (real_of_num (NUMERAL 0)).
Definition term71 (x0 : real -> real) (x1 : real) := fun y0 : real => (real_sub (x0 y0) x1) = (real_of_num (NUMERAL 0)).
Definition term89 (x0 : real) := polynomial_function (fun y0 : real => x0).
Definition term74 (x0 : real -> real) (x1 : real) := ~ (forall y0 : real, (x0 y0) = x1).
Definition term196 (x0 : real -> real) (x1 : nat) (x2 : nat -> real) (x3 : real) := (fun y0 : real => (x0 y0) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x2 y1) (real_pow y0 y1)))) x3.
Definition term272 (x0 : real) (x1 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term132 (x0 : real -> real) (x1 : real) := real_sub (x0 x1).
Definition term252 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) (x4 : nat) := (@IN nat x4 (dotdot (NUMERAL 0) x0)) -> (real_mul (x1 x4) (real_pow x2 x4)) = (x3 x4).
Definition term148 := forall y0 : real, True.
Definition term247 (x0 : nat -> real) (x1 : real) (x2 : nat) := real_mul (x0 x2) (real_pow x1 x2).
Definition term238 (x0 : nat) (x1 : nat -> real) (x2 : Prop) := ((forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) = x2) -> ((~ (exists y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y0) = (real_of_num (NUMERAL 0)))))) -> forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) = ((forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0))) -> x2).
Definition term194 (x0 : nat) (x1 : nat -> real) := @FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (x1 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1)).
Definition term121 (x0 : real -> real) (x1 : real) := @FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (((fun y2 : real => real_sub (x0 y2) x1) y1) = (real_of_num (NUMERAL 0))) y1)).
Definition term98 (x0 : real -> real) := @FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1)).
Definition term67 (x0 : real -> real) (x1 : real) := @FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((real_sub (x0 y1) x1) = (real_of_num (NUMERAL 0))) y1)).
Definition term66 (x0 : real -> real) (x1 : real) := @FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = x1) y1)).
Definition term263 (x0 : nat) (x1 : nat -> real) := @sum nat (dotdot (NUMERAL 0) x0) x1.
Definition term181 (x0 : real) := fun y0 : real => @SETSPEC real x0 True y0.
Definition term150 (x0 : Prop) := forall y0 : real, x0.
Definition term12 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ (~ x1)).
Definition term139 (x0 : real -> real) (x1 : real) := imp ((polynomial_function x0) /\ (polynomial_function (fun y0 : real => x1))).
Definition term39 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (y1 -> y0) = ((~ y0) -> ~ y1)) x0.
Definition term208 (x0 : real -> real) := fun y0 : real => (x0 y0) = (real_of_num (NUMERAL 0)).
Definition term50 := forall y0 : real, forall y1 : real, (y0 = y1) = ((real_sub y0 y1) = (real_of_num (NUMERAL 0))).
Definition term49 := forall y0 : real, forall y1 : real, ((real_sub y0 y1) = (real_of_num (NUMERAL 0))) = (y0 = y1).
Definition term136 (x0 : real -> real) (x1 : real) := polynomial_function (fun y0 : real => real_sub (x0 y0) x1).
Definition term156 (x0 : real -> real) (x1 : nat) := exists y0 : nat -> real, forall y1 : real, (x0 y1) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term146 (x0 : real -> real) := (polynomial_function x0) -> True.
Definition term176 (x0 : real -> real) (x1 : real) := @eq real (x0 x1).
Definition term188 (x0 : real -> real) := (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))) -> (~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1)))) = True.
Definition term93 (x0 : real -> real) (x1 : real -> real) := ((polynomial_function x0) /\ (polynomial_function x1)) -> polynomial_function (fun y0 : real => real_sub (x0 y0) (x1 y0)).
Definition term179 (x0 : real) (x1 : real -> real) (x2 : real) := @SETSPEC real x0 ((x1 x2) = (real_of_num (NUMERAL 0))) x2.
Definition term286 (x0 : nat) (x1 : real) := @eq real (@sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow x1 y0))).
Definition term198 (x0 : nat) (x1 : nat -> real) (x2 : real) := @eq real (@sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_mul (x1 y0) (real_pow x2 y0))).
Definition term82 (x0 : real -> real) := forall y0 : real, (polynomial_function x0) -> (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((real_sub (x0 y2) y0) = (real_of_num (NUMERAL 0))) y2))) = (~ (forall y1 : real, (real_sub (x0 y1) y0) = (real_of_num (NUMERAL 0)))).
Definition term81 (x0 : real -> real) := forall y0 : real, (polynomial_function x0) -> (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((x0 y2) = y0) y2))) = (~ (forall y1 : real, (x0 y1) = y0)).
Definition term244 (x0 : nat -> real) (x1 : real) := fun y0 : nat => real_mul (x0 y0) (real_pow x1 y0).
Definition term145 (x0 : real) (x1 : real -> real) := ((polynomial_function x1) -> ((@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((real_sub (x1 y1) x0) = (real_of_num (NUMERAL 0))) y1))) = (~ (forall y0 : real, (real_sub (x1 y0) x0) = (real_of_num (NUMERAL 0))))) = True) -> ((polynomial_function x1) -> (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((real_sub (x1 y1) x0) = (real_of_num (NUMERAL 0))) y1))) = (~ (forall y0 : real, (real_sub (x1 y0) x0) = (real_of_num (NUMERAL 0))))) = ((polynomial_function x1) -> True).
Definition term207 (x0 : nat) (x1 : nat -> real) := imp (~ (exists y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y0) = (real_of_num (NUMERAL 0)))))).
Definition term36 := fun y0 : Prop => forall y1 : Prop, (y1 -> y0) = ((~ y0) -> ~ y1).
Definition term128 (x0 : real -> real) (x1 : real -> real) := ((polynomial_function x0) /\ (polynomial_function x1)) -> (polynomial_function (fun y0 : real => real_sub (x0 y0) (x1 y0))) = True.
Definition term142 (x0 : real -> real) (x1 : real) := (polynomial_function x0) /\ (polynomial_function (fun y0 : real => x1)).
Definition term30 (x0 : Prop) (x1 : Prop) := (~ x0) -> ~ x1.
Definition term94 (x0 : real -> real) (x1 : real -> real) := (polynomial_function x0) /\ (polynomial_function x1).
Definition term90 (x0 : real -> real) := (fun y0 : real -> real => forall y1 : real -> real, ((polynomial_function y0) /\ (polynomial_function y1)) -> polynomial_function (fun y2 : real => real_sub (y0 y2) (y1 y2))) x0.
Definition term167 (x0 : real -> real) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((~ (~ (forall y1 : real, (x0 y1) = (real_of_num (NUMERAL 0))))) = x1) -> (x1 -> (~ (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((x0 y2) = (real_of_num (NUMERAL 0))) y2)))) = y0) -> ((~ (~ (forall y1 : real, (x0 y1) = (real_of_num (NUMERAL 0))))) -> ~ (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((x0 y2) = (real_of_num (NUMERAL 0))) y2)))) = (x1 -> y0)) x2.
Definition term54 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real) := @SETSPEC real x0 ((x1 x2) = x3).
Definition term14 (x0 : Prop) := (fun y0 : Prop => (~ (y0 /\ (~ x0))) = (y0 -> x0)) False.
Definition term173 (x0 : real -> Prop) := ~ (@FINITE real x0).
Definition term100 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term183 (x0 : real) := exists y0 : real, @SETSPEC real x0 True y0.
Definition term91 (x0 : real -> real) := forall y0 : real -> real, ((polynomial_function x0) /\ (polynomial_function y0)) -> polynomial_function (fun y1 : real => real_sub (x0 y1) (y0 y1)).
Definition term107 (x0 : real -> real) (x1 : real) (x2 : Prop) (x3 : Prop) := ((polynomial_function x0) = x2) -> (x2 -> ((@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((real_sub (x0 y1) x1) = (real_of_num (NUMERAL 0))) y1))) = (~ (forall y0 : real, (real_sub (x0 y0) x1) = (real_of_num (NUMERAL 0))))) = x3) -> ((polynomial_function x0) -> (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((real_sub (x0 y1) x1) = (real_of_num (NUMERAL 0))) y1))) = (~ (forall y0 : real, (real_sub (x0 y0) x1) = (real_of_num (NUMERAL 0))))) = (x2 -> x3).
Definition term48 := fun y0 : real => forall y1 : real, (y0 = y1) = ((real_sub y0 y1) = (real_of_num (NUMERAL 0))).
Definition term250 (x0 : nat) (x1 : nat) := imp (@IN nat x0 (dotdot (NUMERAL 0) x1)).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term251 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) (x4 : nat) := (@IN nat x4 (dotdot (NUMERAL 0) x0)) -> ((fun y0 : nat => real_mul (x1 y0) (real_pow x2 y0)) x4) = (x3 x4).
Definition term294 (x0 : nat -> Prop) := @sum nat x0 (fun y0 : nat => real_of_num (NUMERAL 0)).
Definition term157 (x0 : real -> real) (x1 : nat) (x2 : nat -> real) := forall y0 : real, (x0 y0) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x2 y1) (real_pow y0 y1))).
Definition term273 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat) := (@IN nat x3 (dotdot (NUMERAL 0) x0)) -> (real_mul (x1 x3) (real_pow x2 x3)) = (real_mul (real_of_num (NUMERAL 0)) (real_pow x2 x3)).
Definition term224 (x0 : nat) (x1 : nat -> real) := fun y0 : nat => (fun y1 : nat => (@IN nat y1 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0))))) y0.
Definition term160 (x0 : real -> real) := (~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0)))) -> @FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1)).
Definition term296 (x0 : nat) (x1 : nat -> real) := (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0))) -> True.
Definition term190 (x0 : real -> real) := (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))) -> True.
Definition term295 (x0 : nat) (x1 : nat -> real) := imp (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0))).
Definition term283 (x0 : nat) (x1 : nat -> real) (x2 : real) := imp (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = (real_mul (real_of_num (NUMERAL 0)) (real_pow x2 y0))).
Definition term282 (x0 : nat) (x1 : nat -> real) (x2 : real) := imp (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = ((fun y1 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow x2 y1)) y0)).
Definition term258 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) := imp (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = (x3 y0)).
Definition term257 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) := imp (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> ((fun y1 : nat => real_mul (x1 y1) (real_pow x2 y1)) y0) = (x3 y0)).
Definition term130 (x0 : real) := fun y0 : real => x0.
Definition term151 := fun y0 : real -> real => True.
Definition term137 (x0 : real -> real) (x1 : real) := @eq Prop (polynomial_function (fun y0 : real => real_sub (x0 y0) ((fun y1 : real => x1) y0))).
Definition term177 := @eq real (real_of_num (NUMERAL 0)).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term262 (x0 : nat) (x1 : nat -> real) (x2 : real) := @eq real (@sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => (fun y1 : nat => real_mul (x1 y1) (real_pow x2 y1)) y0)).
Definition term259 (x0 : nat -> real) (x1 : real) := fun y0 : nat => (fun y1 : nat => real_mul (x0 y1) (real_pow x1 y1)) y0.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@sum a0 y0 (fun y1 : a0 => real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) x0.
Definition term134 (x0 : real -> real) (x1 : real) := fun y0 : real => real_sub (x0 y0) ((fun y1 : real => x1) y0).
Definition term187 (a0 : Type') := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 True y1).
Definition term152 := forall y0 : real -> real, True.
Definition term13 (x0 : Prop) (x1 : Prop) := @eq Prop ((~ (x0 /\ (~ x1))) = (x0 -> x1)).
Definition term171 (x0 : real -> real) (x1 : Prop) := ((forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))) -> (~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1)))) = x1) -> ((~ (~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))))) -> ~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1)))) = ((forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))) -> x1).
Definition term96 (x0 : real -> real) := (fun y0 : real -> real => (polynomial_function y0) -> (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((y0 y2) = (real_of_num (NUMERAL 0))) y2))) = (~ (forall y1 : real, (y0 y1) = (real_of_num (NUMERAL 0))))) x0.
Definition term287 (x0 : nat) := fun y0 : real => (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow y0 y1))) = (real_of_num (NUMERAL 0)).
Definition term209 (x0 : nat) (x1 : nat -> real) := fun y0 : real => (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0)).
Definition term200 (x0 : real) (x1 : nat) (x2 : nat -> real) (x3 : real) := @SETSPEC real x0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y0 : nat => real_mul (x2 y0) (real_pow x3 y0))) = (real_of_num (NUMERAL 0))) x3.
Definition term144 (x0 : real -> real) (x1 : real) := (polynomial_function x0) -> ((@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((real_sub (x0 y1) x1) = (real_of_num (NUMERAL 0))) y1))) = (~ (forall y0 : real, (real_sub (x0 y0) x1) = (real_of_num (NUMERAL 0))))) = True.
Definition term116 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real) := @SETSPEC real x0 (((fun y0 : real => real_sub (x1 y0) x2) x3) = (real_of_num (NUMERAL 0))) x3.
Definition term228 (x0 : nat) (x1 : nat -> real) (x2 : nat) := ~ ((fun y0 : nat => (@IN nat y0 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y0) = (real_of_num (NUMERAL 0))))) x2).
Definition term95 (x0 : real -> real) (x1 : real -> real) := polynomial_function (fun y0 : real => real_sub (x0 y0) (x1 y0)).
Definition term131 (x0 : real) (x1 : real) := (fun y0 : real => x0) x1.
Definition term92 (x0 : real -> real) (x1 : real -> real) := (fun y0 : real -> real => ((polynomial_function x0) /\ (polynomial_function y0)) -> polynomial_function (fun y1 : real => real_sub (x0 y1) (y0 y1))) x1.
Definition term215 (x0 : nat) (x1 : nat -> real) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((~ (exists y1 : nat, (@IN nat y1 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0)))))) = x2) -> (x2 -> (forall y1 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (x1 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) = y0) -> ((~ (exists y1 : nat, (@IN nat y1 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0)))))) -> forall y1 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (x1 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) = (x2 -> y0)) x3.
Definition term106 (x0 : real -> real) (x1 : real) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((polynomial_function x0) = x2) -> (x2 -> ((@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((real_sub (x0 y2) x1) = (real_of_num (NUMERAL 0))) y2))) = (~ (forall y1 : real, (real_sub (x0 y1) x1) = (real_of_num (NUMERAL 0))))) = y0) -> ((polynomial_function x0) -> (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((real_sub (x0 y2) x1) = (real_of_num (NUMERAL 0))) y2))) = (~ (forall y1 : real, (real_sub (x0 y1) x1) = (real_of_num (NUMERAL 0))))) = (x2 -> y0)) x3.
Definition term60 (x0 : real) (x1 : real -> real) (x2 : real) := exists y0 : real, @SETSPEC real x0 ((x1 y0) = x2) y0.
Definition term10 (x0 : Prop) := ~ (True /\ (~ x0)).
Definition term293 (x0 : nat) := @sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_of_num (NUMERAL 0)).
Definition term16 (x0 : Prop) := True /\ (~ x0).
Definition term281 (x0 : nat) (x1 : nat -> real) (x2 : real) := forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = ((fun y1 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow x2 y1)) y0).
Definition term47 := fun y0 : real => forall y1 : real, ((real_sub y0 y1) = (real_of_num (NUMERAL 0))) = (y0 = y1).
Definition term15 (x0 : Prop) := ~ (False /\ (~ x0)).
Definition term218 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term280 (x0 : nat) (x1 : nat -> real) (x2 : real) := fun y0 : nat => (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = (real_mul (real_of_num (NUMERAL 0)) (real_pow x2 y0)).
Definition term56 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real) := @SETSPEC real x0 ((x1 x3) = x2) x3.
Definition term57 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real) := @SETSPEC real x0 ((real_sub (x1 x3) x2) = (real_of_num (NUMERAL 0))) x3.
Definition term51 (x0 : real) := (fun y0 : real => forall y1 : real, (y0 = y1) = ((real_sub y0 y1) = (real_of_num (NUMERAL 0)))) x0.
Definition term52 (x0 : real) (x1 : real) := (fun y0 : real => (x0 = y0) = ((real_sub x0 y0) = (real_of_num (NUMERAL 0)))) x1.
Definition term299 (x0 : real -> real) := fun y0 : nat => exists y1 : nat -> real, forall y2 : real, (x0 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term289 (x0 : nat -> real) (x1 : nat) := (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x1)) -> (x0 y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x0 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) = (forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))).
Definition term240 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := (forall y0 : a0, (@IN a0 y0 x1) -> (x0 y0) = (x2 y0)) -> (@sum a0 x1 (fun y0 : a0 => x0 y0)) = (@sum a0 x1 x2).
Definition term203 (x0 : nat) (x1 : nat -> real) := fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (x1 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1.
Definition term184 (x0 : real -> real) := fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1.
Definition term119 (x0 : real -> real) (x1 : real) := fun y0 : real => exists y1 : real, @SETSPEC real y0 (((fun y2 : real => real_sub (x0 y2) x1) y1) = (real_of_num (NUMERAL 0))) y1.
Definition term63 (x0 : real -> real) (x1 : real) := fun y0 : real => exists y1 : real, @SETSPEC real y0 ((real_sub (x0 y1) x1) = (real_of_num (NUMERAL 0))) y1.
Definition term62 (x0 : real -> real) (x1 : real) := fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = x1) y1.
Definition term229 (x0 : nat) (x1 : nat -> real) (x2 : nat) := ~ ((@IN nat x2 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 x2) = (real_of_num (NUMERAL 0))))).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term248 (x0 : nat -> real) (x1 : real) (x2 : nat) := @eq real ((fun y0 : nat => real_mul (x0 y0) (real_pow x1 y0)) x2).
Definition term245 (x0 : nat) := dotdot (NUMERAL 0) x0.
Definition term219 (x0 : nat) (x1 : nat -> real) := ~ (exists y0 : nat, (fun y1 : nat => (@IN nat y1 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0))))) y0).
Definition term163 (x0 : real -> real) := ~ (~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0)))).
Definition term11 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (~ (y0 /\ (~ x0))) = (y0 -> x0)) x1).
Definition term239 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (fun y0 : nat => (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0))) x2.
Definition term97 (x0 : real -> real) := (polynomial_function x0) -> (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1))) = (~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0)))).
Definition term78 (x0 : real -> real) (x1 : real) := (polynomial_function x0) -> (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((real_sub (x0 y1) x1) = (real_of_num (NUMERAL 0))) y1))) = (~ (forall y0 : real, (real_sub (x0 y0) x1) = (real_of_num (NUMERAL 0)))).
Definition term77 (x0 : real -> real) (x1 : real) := (polynomial_function x0) -> (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = x1) y1))) = (~ (forall y0 : real, (x0 y0) = x1)).
Definition term291 (x0 : nat -> real) (x1 : nat) := (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x1)) -> (x0 y0) = (real_of_num (NUMERAL 0))) -> forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow y0 y1))) = (real_of_num (NUMERAL 0)).
Definition term214 (x0 : nat) (x1 : nat -> real) (x2 : Prop) := forall y0 : Prop, ((~ (exists y1 : nat, (@IN nat y1 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0)))))) = x2) -> (x2 -> (forall y1 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (x1 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) = y0) -> ((~ (exists y1 : nat, (@IN nat y1 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0)))))) -> forall y1 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (x1 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) = (x2 -> y0).
Definition term166 (x0 : real -> real) (x1 : Prop) := forall y0 : Prop, ((~ (~ (forall y1 : real, (x0 y1) = (real_of_num (NUMERAL 0))))) = x1) -> (x1 -> (~ (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((x0 y2) = (real_of_num (NUMERAL 0))) y2)))) = y0) -> ((~ (~ (forall y1 : real, (x0 y1) = (real_of_num (NUMERAL 0))))) -> ~ (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((x0 y2) = (real_of_num (NUMERAL 0))) y2)))) = (x1 -> y0).
Definition term105 (x0 : real -> real) (x1 : real) (x2 : Prop) := forall y0 : Prop, ((polynomial_function x0) = x2) -> (x2 -> ((@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((real_sub (x0 y2) x1) = (real_of_num (NUMERAL 0))) y2))) = (~ (forall y1 : real, (real_sub (x0 y1) x1) = (real_of_num (NUMERAL 0))))) = y0) -> ((polynomial_function x0) -> (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((real_sub (x0 y2) x1) = (real_of_num (NUMERAL 0))) y2))) = (~ (forall y1 : real, (real_sub (x0 y1) x1) = (real_of_num (NUMERAL 0))))) = (x2 -> y0).
Definition term101 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term112 (x0 : real -> real) (x1 : real) (x2 : real) := (fun y0 : real => real_sub (x0 y0) x1) x2.
Definition term7 (x0 : Prop) := fun y0 : Prop => (~ (y0 /\ (~ x0))) = (y0 -> x0).
Definition term43 (x0 : real) := fun y0 : real => ((real_sub x0 y0) = (real_of_num (NUMERAL 0))) = (x0 = y0).
Definition term216 (x0 : nat) (x1 : nat -> real) (x2 : Prop) (x3 : Prop) := ((~ (exists y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y0) = (real_of_num (NUMERAL 0)))))) = x2) -> (x2 -> (forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) = x3) -> ((~ (exists y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y0) = (real_of_num (NUMERAL 0)))))) -> forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) = (x2 -> x3).
Definition term195 (x0 : nat) (x1 : nat -> real) := exists y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y0) = (real_of_num (NUMERAL 0)))).
Definition term3 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term211 (x0 : nat) (x1 : nat -> real) := (~ (exists y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y0) = (real_of_num (NUMERAL 0)))))) -> forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0)).
Definition term254 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) := fun y0 : nat => (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = (x3 y0).
Definition term225 (x0 : nat) (x1 : nat -> real) := exists y0 : nat, (fun y1 : nat => (@IN nat y1 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0))))) y0.
Definition term288 (x0 : nat) := forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow y0 y1))) = (real_of_num (NUMERAL 0)).
Definition term210 (x0 : nat) (x1 : nat -> real) := forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0)).
Definition term6 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term271 := real_mul (real_of_num (NUMERAL 0)).
Definition term212 (x0 : nat) (x1 : nat -> real) := forall y0 : Prop, forall y1 : Prop, ((~ (exists y2 : nat, (@IN nat y2 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y2) = (real_of_num (NUMERAL 0)))))) = y0) -> (y0 -> (forall y2 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y3 : nat => real_mul (x1 y3) (real_pow y2 y3))) = (real_of_num (NUMERAL 0))) = y1) -> ((~ (exists y2 : nat, (@IN nat y2 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y2) = (real_of_num (NUMERAL 0)))))) -> forall y2 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y3 : nat => real_mul (x1 y3) (real_pow y2 y3))) = (real_of_num (NUMERAL 0))) = (y0 -> y1).
Definition term162 (x0 : real -> real) := forall y0 : Prop, forall y1 : Prop, ((~ (~ (forall y2 : real, (x0 y2) = (real_of_num (NUMERAL 0))))) = y0) -> (y0 -> (~ (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((x0 y3) = (real_of_num (NUMERAL 0))) y3)))) = y1) -> ((~ (~ (forall y2 : real, (x0 y2) = (real_of_num (NUMERAL 0))))) -> ~ (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((x0 y3) = (real_of_num (NUMERAL 0))) y3)))) = (y0 -> y1).
Definition term103 (x0 : real -> real) (x1 : real) := forall y0 : Prop, forall y1 : Prop, ((polynomial_function x0) = y0) -> (y0 -> ((@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((real_sub (x0 y3) x1) = (real_of_num (NUMERAL 0))) y3))) = (~ (forall y2 : real, (real_sub (x0 y2) x1) = (real_of_num (NUMERAL 0))))) = y1) -> ((polynomial_function x0) -> (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((real_sub (x0 y3) x1) = (real_of_num (NUMERAL 0))) y3))) = (~ (forall y2 : real, (real_sub (x0 y2) x1) = (real_of_num (NUMERAL 0))))) = (y0 -> y1).
Definition term102 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term38 := forall y0 : Prop, forall y1 : Prop, (y1 -> y0) = ((~ y0) -> ~ y1).
Definition term37 := forall y0 : Prop, forall y1 : Prop, ((~ y0) -> ~ y1) = (y1 -> y0).
Definition term192 (x0 : nat) := forall y0 : nat -> real, (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y3 : nat => real_mul (y0 y3) (real_pow y2 y3))) = (real_of_num (NUMERAL 0))) y2))) = (exists y1 : nat, (@IN nat y1 (dotdot (NUMERAL 0) x0)) /\ (~ ((y0 y1) = (real_of_num (NUMERAL 0))))).
Definition term193 (x0 : nat) (x1 : nat -> real) := (fun y0 : nat -> real => (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y3 : nat => real_mul (y0 y3) (real_pow y2 y3))) = (real_of_num (NUMERAL 0))) y2))) = (exists y1 : nat, (@IN nat y1 (dotdot (NUMERAL 0) x0)) /\ (~ ((y0 y1) = (real_of_num (NUMERAL 0)))))) x1.
Definition term126 (x0 : real -> real) (x1 : real) := imp (polynomial_function (fun y0 : real => real_sub (x0 y0) x1)).
Definition term27 (a0 : Type') := forall y0 : a0 -> Prop, (@INFINITE a0 y0) = (~ (@FINITE a0 y0)).
Definition term267 (x0 : nat -> real) (x1 : real) (x2 : nat) := fun y0 : nat -> real => (forall y1 : nat, (@IN nat y1 (dotdot (NUMERAL 0) x2)) -> (real_mul (x0 y1) (real_pow x1 y1)) = (y0 y1)) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y1 : nat => real_mul (x0 y1) (real_pow x1 y1))) = (@sum nat (dotdot (NUMERAL 0) x2) y0).
Definition term266 (x0 : nat -> real) (x1 : real) (x2 : nat) := fun y0 : nat -> real => (forall y1 : nat, (@IN nat y1 (dotdot (NUMERAL 0) x2)) -> ((fun y2 : nat => real_mul (x0 y2) (real_pow x1 y2)) y1) = (y0 y1)) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y1 : nat => (fun y2 : nat => real_mul (x0 y2) (real_pow x1 y2)) y1)) = (@sum nat (dotdot (NUMERAL 0) x2) y0).
Definition term276 (x0 : real) := fun y0 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow x0 y0).
Definition term253 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) := fun y0 : nat => (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> ((fun y1 : nat => real_mul (x1 y1) (real_pow x2 y1)) y0) = (x3 y0).
Definition term127 (x0 : real -> real) (x1 : real) := (polynomial_function (fun y0 : real => real_sub (x0 y0) x1)) -> (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((real_sub (x0 y1) x1) = (real_of_num (NUMERAL 0))) y1))) = (~ (forall y0 : real, (real_sub (x0 y0) x1) = (real_of_num (NUMERAL 0)))).
Definition term110 (x0 : real -> real) (x1 : real) := (polynomial_function (fun y0 : real => real_sub (x0 y0) x1)) -> (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (((fun y2 : real => real_sub (x0 y2) x1) y1) = (real_of_num (NUMERAL 0))) y1))) = (~ (forall y0 : real, ((fun y1 : real => real_sub (x0 y1) x1) y0) = (real_of_num (NUMERAL 0)))).
Definition term277 (x0 : real) (x1 : nat) := (fun y0 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow x0 y0)) x1.
Definition term70 (x0 : real -> real) (x1 : real) := fun y0 : real => (x0 y0) = x1.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := @sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL 0)).
Definition term26 (a0 : Type') := fun y0 : a0 -> Prop => (~ (@FINITE a0 y0)) = (@INFINITE a0 y0).
Definition term86 := forall y0 : real -> real, forall y1 : real, (polynomial_function y0) -> (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((real_sub (y0 y3) y1) = (real_of_num (NUMERAL 0))) y3))) = (~ (forall y2 : real, (real_sub (y0 y2) y1) = (real_of_num (NUMERAL 0)))).
Definition term85 := forall y0 : real -> real, forall y1 : real, (polynomial_function y0) -> (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((y0 y3) = y1) y3))) = (~ (forall y2 : real, (y0 y2) = y1)).
Definition term220 (x0 : nat) (x1 : nat -> real) := forall y0 : nat, ~ ((fun y1 : nat => (@IN nat y1 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0))))) y0).
Definition term174 (x0 : real -> real) := @INFINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1)).
Definition term25 (a0 : Type') := fun y0 : a0 -> Prop => (@INFINITE a0 y0) = (~ (@FINITE a0 y0)).
Definition term143 (x0 : real -> real) (x1 : real) := @eq Prop (~ (forall y0 : real, (real_sub (x0 y0) x1) = (real_of_num (NUMERAL 0)))).
Definition term53 (x0 : real -> real) (x1 : real) (x2 : real) := real_sub (x0 x1) x2.
Definition term84 := fun y0 : real -> real => forall y1 : real, (polynomial_function y0) -> (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((real_sub (y0 y3) y1) = (real_of_num (NUMERAL 0))) y3))) = (~ (forall y2 : real, (real_sub (y0 y2) y1) = (real_of_num (NUMERAL 0)))).
Definition term83 := fun y0 : real -> real => forall y1 : real, (polynomial_function y0) -> (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((y0 y3) = y1) y3))) = (~ (forall y2 : real, (y0 y2) = y1)).
Definition term114 (x0 : real -> real) (x1 : real) (x2 : real) := @eq real (real_sub (x0 x1) x2).
Definition term122 (x0 : real -> real) (x1 : real) := @eq Prop (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (((fun y2 : real => real_sub (x0 y2) x1) y1) = (real_of_num (NUMERAL 0))) y1))).
Definition term69 (x0 : real -> real) (x1 : real) := @eq Prop (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((real_sub (x0 y1) x1) = (real_of_num (NUMERAL 0))) y1))).
Definition term68 (x0 : real -> real) (x1 : real) := @eq Prop (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = x1) y1))).
Definition term72 (x0 : real -> real) (x1 : real) := forall y0 : real, (x0 y0) = x1.
Definition term189 (x0 : real -> real) := ((forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))) -> (~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1)))) = True) -> ((~ (~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))))) -> ~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1)))) = ((forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))) -> True).
Definition term261 (x0 : nat) (x1 : nat -> real) (x2 : real) := @sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => (fun y1 : nat => real_mul (x1 y1) (real_pow x2 y1)) y0).
Definition term202 (x0 : real) (x1 : nat) (x2 : nat -> real) := exists y0 : real, @SETSPEC real x0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x2 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) y0.
Definition term182 (x0 : real) (x1 : real -> real) := exists y0 : real, @SETSPEC real x0 ((x1 y0) = (real_of_num (NUMERAL 0))) y0.
Definition term118 (x0 : real) (x1 : real -> real) (x2 : real) := exists y0 : real, @SETSPEC real x0 (((fun y1 : real => real_sub (x1 y1) x2) y0) = (real_of_num (NUMERAL 0))) y0.
Definition term61 (x0 : real) (x1 : real -> real) (x2 : real) := exists y0 : real, @SETSPEC real x0 ((real_sub (x1 y0) x2) = (real_of_num (NUMERAL 0))) y0.
Definition term18 (x0 : Prop) := @eq Prop (~ (True /\ (~ x0))).
Definition term133 (x0 : real -> real) (x1 : real) (x2 : real) := real_sub (x0 x2) ((fun y0 : real => x1) x2).
Definition term153 (x0 : Prop) := forall y0 : real -> real, x0.
Definition term31 (x0 : Prop) := fun y0 : Prop => ((~ x0) -> ~ y0) = (y0 -> x0).
Definition term87 := forall y0 : real -> real, (polynomial_function y0) -> (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((y0 y2) = (real_of_num (NUMERAL 0))) y2))) = (~ (forall y1 : real, (y0 y1) = (real_of_num (NUMERAL 0)))).
Definition term20 (x0 : Prop) := @eq Prop (~ (False /\ (~ x0))).
Definition term237 (x0 : nat) (x1 : nat -> real) (x2 : Prop) := ((~ (exists y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y0) = (real_of_num (NUMERAL 0)))))) = (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0)))) -> ((forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0))) -> (forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) = x2) -> ((~ (exists y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y0) = (real_of_num (NUMERAL 0)))))) -> forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) = ((forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0))) -> x2).
Definition term4 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term44 (x0 : real) := fun y0 : real => (x0 = y0) = ((real_sub x0 y0) = (real_of_num (NUMERAL 0))).
Definition term154 (x0 : real -> real) := imp (exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (x0 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3)))).
Definition term172 (x0 : real -> real) (x1 : real) := (fun y0 : real => (x0 y0) = (real_of_num (NUMERAL 0))) x1.
Definition term256 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) := forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = (x3 y0).
Definition term255 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) := forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> ((fun y1 : nat => real_mul (x1 y1) (real_pow x2 y1)) y0) = (x3 y0).
Definition term138 (x0 : real -> real) (x1 : real) := @eq Prop (polynomial_function (fun y0 : real => real_sub (x0 y0) x1)).
Definition term170 (x0 : real -> real) (x1 : Prop) := ((~ (~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))))) = (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0)))) -> ((forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))) -> (~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1)))) = x1) -> ((~ (~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))))) -> ~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1)))) = ((forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))) -> x1).
Definition term249 (x0 : nat -> real) (x1 : real) (x2 : nat) := @eq real (real_mul (x0 x2) (real_pow x1 x2)).
Definition term113 (x0 : real -> real) (x1 : real) (x2 : real) := @eq real ((fun y0 : real => real_sub (x0 y0) x1) x2).
Definition term55 (x0 : real) (x1 : real -> real) (x2 : real) (x3 : real) := @SETSPEC real x0 ((real_sub (x1 x2) x3) = (real_of_num (NUMERAL 0))).
Definition term165 (x0 : real -> real) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (~ (forall y2 : real, (x0 y2) = (real_of_num (NUMERAL 0))))) = y0) -> (y0 -> (~ (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((x0 y3) = (real_of_num (NUMERAL 0))) y3)))) = y1) -> ((~ (~ (forall y2 : real, (x0 y2) = (real_of_num (NUMERAL 0))))) -> ~ (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((x0 y3) = (real_of_num (NUMERAL 0))) y3)))) = (y0 -> y1)) x1.
Definition term169 (x0 : real -> real) := forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0)).
Definition term58 (x0 : real) (x1 : real -> real) (x2 : real) := fun y0 : real => @SETSPEC real x0 ((x1 y0) = x2) y0.
Definition term9 (x0 : Prop) := (fun y0 : Prop => (~ (y0 /\ (~ x0))) = (y0 -> x0)) True.
Definition term232 (x0 : nat) (x1 : nat -> real) := forall y0 : nat, ~ ((@IN nat y0 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y0) = (real_of_num (NUMERAL 0))))).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (@FINITE a0 y0)) = (@INFINITE a0 y0)) x0.
Definition term206 (x0 : real -> real) := imp (~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1)))).
Definition term268 (x0 : nat -> real) (x1 : real) (x2 : nat) := forall y0 : nat -> real, (forall y1 : nat, (@IN nat y1 (dotdot (NUMERAL 0) x2)) -> (real_mul (x0 y1) (real_pow x1 y1)) = (y0 y1)) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y1 : nat => real_mul (x0 y1) (real_pow x1 y1))) = (@sum nat (dotdot (NUMERAL 0) x2) y0).
Definition term243 (x0 : nat -> real) (x1 : real) (x2 : nat) := forall y0 : nat -> real, (forall y1 : nat, (@IN nat y1 (dotdot (NUMERAL 0) x2)) -> ((fun y2 : nat => real_mul (x0 y2) (real_pow x1 y2)) y1) = (y0 y1)) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y1 : nat => (fun y2 : nat => real_mul (x0 y2) (real_pow x1 y2)) y1)) = (@sum nat (dotdot (NUMERAL 0) x2) y0).
Definition term242 (x0 : nat -> real) (x1 : nat -> Prop) := forall y0 : nat -> real, (forall y1 : nat, (@IN nat y1 x1) -> (x0 y1) = (y0 y1)) -> (@sum nat x1 (fun y1 : nat => x0 y1)) = (@sum nat x1 y0).
Definition term217 (x0 : nat -> Prop) := ~ (exists y0 : nat, x0 y0).
Definition term42 (x0 : real -> real) := exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (x0 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term140 (x0 : real -> real) (x1 : real) := ((polynomial_function x0) /\ (polynomial_function (fun y0 : real => x1))) -> (polynomial_function (fun y0 : real => real_sub (x0 y0) x1)) = True.
Definition term129 (x0 : real -> real) (x1 : real) := ((polynomial_function x0) /\ (polynomial_function (fun y0 : real => x1))) -> (polynomial_function (fun y0 : real => real_sub (x0 y0) ((fun y1 : real => x1) y0))) = True.
Definition term274 (x0 : nat) (x1 : nat -> real) (x2 : real) := forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = (real_mul (real_of_num (NUMERAL 0)) (real_pow x2 y0)).
Definition term230 (x0 : nat) (x1 : nat -> real) := fun y0 : nat => ~ ((fun y1 : nat => (@IN nat y1 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y1) = (real_of_num (NUMERAL 0))))) y0).
Definition term234 (x0 : nat) (x1 : nat) := @IN nat x0 (dotdot (NUMERAL 0) x1).
Definition term231 (x0 : nat) (x1 : nat -> real) := fun y0 : nat => ~ ((@IN nat y0 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y0) = (real_of_num (NUMERAL 0))))).
Definition term278 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat) := (@IN nat x3 (dotdot (NUMERAL 0) x0)) -> (real_mul (x1 x3) (real_pow x2 x3)) = ((fun y0 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow x2 y0)) x3).
Definition term164 (x0 : real -> real) := ~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1))).
Definition term159 (x0 : real -> real) := (~ (~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))))) -> ~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1))).
Definition term76 (x0 : real -> real) := imp (polynomial_function x0).
Definition term284 (x0 : nat) (x1 : real) := @sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow x1 y0)).
Definition term197 (x0 : nat) (x1 : nat -> real) (x2 : real) := @sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_mul (x1 y0) (real_pow x2 y0)).
Definition term158 (x0 : real -> real) := (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1))) -> ~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))).
Definition term28 (a0 : Type') := forall y0 : a0 -> Prop, (~ (@FINITE a0 y0)) = (@INFINITE a0 y0).
Definition term298 (x0 : real -> real) (x1 : nat) := fun y0 : nat -> real => forall y1 : real, (x0 y1) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term5 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term269 (x0 : nat -> real) (x1 : real) (x2 : nat) (x3 : nat -> real) := (fun y0 : nat -> real => (forall y1 : nat, (@IN nat y1 (dotdot (NUMERAL 0) x2)) -> (real_mul (x0 y1) (real_pow x1 y1)) = (y0 y1)) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y1 : nat => real_mul (x0 y1) (real_pow x1 y1))) = (@sum nat (dotdot (NUMERAL 0) x2) y0)) x3.
Definition term8 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (~ (y0 /\ (~ x0))) = (y0 -> x0)) x1.
Definition term236 (x0 : nat) (x1 : nat -> real) := forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0)).
Definition term168 (x0 : real -> real) (x1 : Prop) (x2 : Prop) := ((~ (~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))))) = x1) -> (x1 -> (~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1)))) = x2) -> ((~ (~ (forall y0 : real, (x0 y0) = (real_of_num (NUMERAL 0))))) -> ~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((x0 y1) = (real_of_num (NUMERAL 0))) y1)))) = (x1 -> x2).
Definition term265 (x0 : nat -> real) (x1 : real) (x2 : nat) (x3 : nat -> real) := (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x2)) -> (real_mul (x0 y0) (real_pow x1 y0)) = (x3 y0)) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y0 : nat => real_mul (x0 y0) (real_pow x1 y0))) = (@sum nat (dotdot (NUMERAL 0) x2) x3).
Definition term264 (x0 : nat -> real) (x1 : real) (x2 : nat) (x3 : nat -> real) := (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x2)) -> ((fun y1 : nat => real_mul (x0 y1) (real_pow x1 y1)) y0) = (x3 y0)) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y0 : nat => (fun y1 : nat => real_mul (x0 y1) (real_pow x1 y1)) y0)) = (@sum nat (dotdot (NUMERAL 0) x2) x3).
Definition term213 (x0 : nat) (x1 : nat -> real) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (exists y2 : nat, (@IN nat y2 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y2) = (real_of_num (NUMERAL 0)))))) = y0) -> (y0 -> (forall y2 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y3 : nat => real_mul (x1 y3) (real_pow y2 y3))) = (real_of_num (NUMERAL 0))) = y1) -> ((~ (exists y2 : nat, (@IN nat y2 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y2) = (real_of_num (NUMERAL 0)))))) -> forall y2 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y3 : nat => real_mul (x1 y3) (real_pow y2 y3))) = (real_of_num (NUMERAL 0))) = (y0 -> y1)) x2.
Definition term104 (x0 : real -> real) (x1 : real) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((polynomial_function x0) = y0) -> (y0 -> ((@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((real_sub (x0 y3) x1) = (real_of_num (NUMERAL 0))) y3))) = (~ (forall y2 : real, (real_sub (x0 y2) x1) = (real_of_num (NUMERAL 0))))) = y1) -> ((polynomial_function x0) -> (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((real_sub (x0 y3) x1) = (real_of_num (NUMERAL 0))) y3))) = (~ (forall y2 : real, (real_sub (x0 y2) x1) = (real_of_num (NUMERAL 0))))) = (y0 -> y1)) x2.
Definition term123 (x0 : real -> real) (x1 : real) := fun y0 : real => ((fun y1 : real => real_sub (x0 y1) x1) y0) = (real_of_num (NUMERAL 0)).
Definition term241 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := forall y0 : a0 -> real, (forall y1 : a0, (@IN a0 y1 x1) -> (x0 y1) = (y0 y1)) -> (@sum a0 x1 (fun y1 : a0 => x0 y1)) = (@sum a0 x1 y0).
Definition term205 (x0 : nat) (x1 : nat -> real) := ~ (exists y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) /\ (~ ((x1 y0) = (real_of_num (NUMERAL 0))))).
Definition term32 (x0 : Prop) := fun y0 : Prop => (y0 -> x0) = ((~ x0) -> ~ y0).
Definition term233 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (@IN nat x2 (dotdot (NUMERAL 0) x0)) -> (x1 x2) = (real_of_num (NUMERAL 0)).
Definition term279 (x0 : nat) (x1 : nat -> real) (x2 : real) := fun y0 : nat => (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = ((fun y1 : nat => real_mul (real_of_num (NUMERAL 0)) (real_pow x2 y1)) y0).
Definition term141 (x0 : real -> real) := and (polynomial_function x0).
Definition term46 (x0 : real) := forall y0 : real, (x0 = y0) = ((real_sub x0 y0) = (real_of_num (NUMERAL 0))).
