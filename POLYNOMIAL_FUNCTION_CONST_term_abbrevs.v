Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term44 (x0 : real) (x1 : nat) := (fun y0 : nat => x0) x1.
Definition term42 (x0 : real) := (fun y0 : nat => x0) (NUMERAL 0).
Definition term55 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term45 (x0 : real) := fun y0 : nat => (fun y1 : nat => x0) y0.
Definition term47 (x0 : real) := @eq real ((fun y0 : nat => x0) (NUMERAL 0)).
Definition term52 := fun y0 : real => True.
Definition term35 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : nat => real_mul ((fun y1 : nat => x0) y0) (real_pow x1 y0)) x2.
Definition term6 (x0 : real -> real) := (fun y0 : real -> real => (polynomial_function y0) = (exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (y0 y3) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4))))) x0.
Definition term13 (x0 : real) (x1 : real) := (fun y0 : real => (fun y1 : real => x0) y0) x1.
Definition term34 (x0 : real) (x1 : real) := (fun y0 : nat => (fun y1 : nat => real_mul ((fun y2 : nat => x0) y1) (real_pow x1 y1)) y0) (NUMERAL 0).
Definition term30 (x0 : real) (x1 : real) := @sum nat (dotdot (NUMERAL 0) (NUMERAL 0)) (fun y0 : nat => real_mul ((fun y1 : nat => x0) y0) (real_pow x1 y0)).
Definition term8 (x0 : real) := polynomial_function (fun y0 : real => x0).
Definition term54 := forall y0 : real, True.
Definition term56 (x0 : Prop) := forall y0 : real, x0.
Definition term15 (x0 : real) := fun y0 : real => (fun y1 : real => x0) y0.
Definition term49 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term48 (x0 : real) := real_mul ((fun y0 : nat => x0) (NUMERAL 0)).
Definition term36 (x0 : real) (x1 : real) (x2 : nat) := real_mul ((fun y0 : nat => x0) x2) (real_pow x1 x2).
Definition term57 (x0 : real) := exists y0 : nat -> real, forall y1 : real, x0 = (@sum nat (dotdot (NUMERAL 0) (NUMERAL 0)) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term26 (x0 : real) (x1 : nat) := exists y0 : nat -> real, forall y1 : real, x0 = (@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term25 (x0 : real) (x1 : nat) := exists y0 : nat -> real, forall y1 : real, ((fun y2 : real => x0) y1) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term4 (x0 : nat -> real) (x1 : nat) := (fun y0 : nat => (@sum nat (dotdot y0 y0) x0) = (x0 y0)) x1.
Definition term53 (x0 : real) := forall y0 : real, x0 = (@sum nat (dotdot (NUMERAL 0) (NUMERAL 0)) (fun y1 : nat => real_mul ((fun y2 : nat => x0) y1) (real_pow y0 y1))).
Definition term22 (x0 : real) (x1 : nat) (x2 : nat -> real) := forall y0 : real, x0 = (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x2 y1) (real_pow y0 y1))).
Definition term3 (x0 : nat -> real) := forall y0 : nat, (@sum nat (dotdot y0 y0) x0) = (x0 y0).
Definition term5 (x0 : nat) (x1 : nat -> real) := @sum nat (dotdot x0 x0) x1.
Definition term10 (x0 : real) := fun y0 : real => x0.
Definition term37 (x0 : real) (x1 : real) := fun y0 : nat => (fun y1 : nat => real_mul ((fun y2 : nat => x0) y1) (real_pow x1 y1)) y0.
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term14 (x0 : real) (x1 : real) := (fun y0 : real => x0) x1.
Definition term33 (x0 : nat -> real) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term19 (x0 : real) (x1 : nat) (x2 : nat -> real) := fun y0 : real => ((fun y1 : real => x0) y0) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x2 y1) (real_pow y0 y1))).
Definition term12 (x0 : real -> real) (x1 : real) := (fun y0 : real => x0 y0) x1.
Definition term39 (x0 : real) (x1 : real) := @eq real ((fun y0 : nat => real_mul ((fun y1 : nat => x0) y0) (real_pow x1 y0)) (NUMERAL 0)).
Definition term28 (x0 : real) := fun y0 : nat => exists y1 : nat -> real, forall y2 : real, x0 = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term27 (x0 : real) := fun y0 : nat => exists y1 : nat -> real, forall y2 : real, ((fun y3 : real => x0) y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term51 (x0 : real) := fun y0 : real => x0 = (@sum nat (dotdot (NUMERAL 0) (NUMERAL 0)) (fun y1 : nat => real_mul ((fun y2 : nat => x0) y1) (real_pow y0 y1))).
Definition term59 := forall y0 : real, polynomial_function (fun y1 : real => y0).
Definition term16 (x0 : real) (x1 : real) := @eq real ((fun y0 : real => (fun y1 : real => x0) y0) x1).
Definition term17 (x0 : real) (x1 : real) := @eq real ((fun y0 : real => x0) x1).
Definition term32 (x0 : real) (x1 : real) := fun y0 : nat => real_mul ((fun y1 : nat => x0) y0) (real_pow x1 y0).
Definition term41 (x0 : real) := (fun y0 : nat => (fun y1 : nat => x0) y0) (NUMERAL 0).
Definition term50 := real_of_num (NUMERAL (BIT1 0)).
Definition term46 (x0 : real) := @eq real ((fun y0 : nat => (fun y1 : nat => x0) y0) (NUMERAL 0)).
Definition term38 (x0 : real) (x1 : real) := @eq real ((fun y0 : nat => (fun y1 : nat => real_mul ((fun y2 : nat => x0) y1) (real_pow x1 y1)) y0) (NUMERAL 0)).
Definition term40 (x0 : real) (x1 : real) := real_mul ((fun y0 : nat => x0) (NUMERAL 0)) (real_pow x1 (NUMERAL 0)).
Definition term31 (x0 : real) (x1 : real) := (fun y0 : nat => real_mul ((fun y1 : nat => x0) y0) (real_pow x1 y0)) (NUMERAL 0).
Definition term1 (x0 : real) := real_mul x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term29 (x0 : real) := exists y0 : nat, exists y1 : nat -> real, forall y2 : real, x0 = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term9 (x0 : real) := exists y0 : nat, exists y1 : nat -> real, forall y2 : real, ((fun y3 : real => x0) y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term7 (x0 : real -> real) := exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (x0 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term2 (x0 : nat -> real) := (fun y0 : nat -> real => forall y1 : nat, (@sum nat (dotdot y1 y1) y0) = (y0 y1)) x0.
Definition term43 (x0 : real) := fun y0 : nat => x0.
Definition term18 (x0 : nat) (x1 : nat -> real) (x2 : real) := @sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_mul (x1 y0) (real_pow x2 y0)).
Definition term0 (x0 : real) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0) x0.
Definition term58 (x0 : real) := fun y0 : nat -> real => forall y1 : real, x0 = (@sum nat (dotdot (NUMERAL 0) (NUMERAL 0)) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term24 (x0 : real) (x1 : nat) := fun y0 : nat -> real => forall y1 : real, x0 = (@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term23 (x0 : real) (x1 : nat) := fun y0 : nat -> real => forall y1 : real, ((fun y2 : real => x0) y1) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term20 (x0 : real) (x1 : nat) (x2 : nat -> real) := fun y0 : real => x0 = (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x2 y1) (real_pow y0 y1))).
Definition term21 (x0 : real) (x1 : nat) (x2 : nat -> real) := forall y0 : real, ((fun y1 : real => x0) y0) = (@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x2 y1) (real_pow y0 y1))).
