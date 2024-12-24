Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : real -> real) := (fun y0 : real -> real => (polynomial_function y0) = (exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (y0 y3) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4))))) x0.
Definition term1 (x0 : real -> real) := (fun y0 : real -> real => exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (y0 y3) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4)))) x0.
Definition term3 := forall y0 : real -> real, (polynomial_function y0) = (exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (y0 y3) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4)))).
Definition term0 := fun y0 : real -> real => exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (y0 y3) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4))).
Definition term2 (x0 : real -> real) := exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (x0 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
