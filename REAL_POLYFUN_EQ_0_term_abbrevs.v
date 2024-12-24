Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term70 (x0 : nat) := Peano.le (@CARD real (@UNIV real)) x0.
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (dotdot x1 x2).
Definition term67 (x0 : nat) (x1 : nat -> real) := @CARD real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (x1 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1)).
Definition term30 (x0 : nat) := (fun y0 : nat => forall y1 : nat -> real, (~ (forall y2 : nat, (@IN nat y2 (dotdot (NUMERAL 0) y0)) -> (y1 y2) = (real_of_num (NUMERAL 0)))) -> (@FINITE real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((@sum nat (dotdot (NUMERAL 0) y0) (fun y4 : nat => real_mul (y1 y4) (real_pow y3 y4))) = (real_of_num (NUMERAL 0))) y3))) /\ (Peano.le (@CARD real (@GSPEC real (fun y2 : real => exists y3 : real, @SETSPEC real y2 ((@sum nat (dotdot (NUMERAL 0) y0) (fun y4 : nat => real_mul (y1 y4) (real_pow y3 y4))) = (real_of_num (NUMERAL 0))) y3))) y0)) x0.
Definition term63 (x0 : real) (x1 : nat) (x2 : nat -> real) := fun y0 : real => @SETSPEC real x0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x2 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) y0.
Definition term31 (x0 : nat) := forall y0 : nat -> real, (~ (forall y1 : nat, (@IN nat y1 (dotdot (NUMERAL 0) x0)) -> (y0 y1) = (real_of_num (NUMERAL 0)))) -> (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y3 : nat => real_mul (y0 y3) (real_pow y2 y3))) = (real_of_num (NUMERAL 0))) y2))) /\ (Peano.le (@CARD real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y3 : nat => real_mul (y0 y3) (real_pow y2 y3))) = (real_of_num (NUMERAL 0))) y2))) x0).
Definition term93 (x0 : nat -> real) (x1 : real) (x2 : nat) := (fun y0 : nat => real_mul (x0 y0) (real_pow x1 y0)) x2.
Definition term126 := fun y0 : nat => real_of_num (NUMERAL 0).
Definition term61 (x0 : real) (x1 : nat) (x2 : nat -> real) (x3 : real) := @SETSPEC real x0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y0 : nat => real_mul (x2 y0) (real_pow x3 y0))) = (real_of_num (NUMERAL 0))).
Definition term120 (x0 : nat -> real) (x1 : nat) := real_mul (x0 x1).
Definition term117 (x0 : nat) (x1 : nat) := (Peano.le (NUMERAL 0) x0) /\ (Peano.le x0 x1).
Definition term16 := fun y0 : real => exists y1 : real, @SETSPEC real y0 True y1.
Definition term107 (x0 : nat) := @sum nat (dotdot (NUMERAL 0) x0).
Definition term34 (x0 : Prop) := ~ (~ x0).
Definition term47 := real_of_num (NUMERAL 0).
Definition term79 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@IN nat y2 (dotdot y0 y1)) = ((Peano.le y0 y2) /\ (Peano.le y2 y1))) x0.
Definition term135 (x0 : nat -> real) (x1 : real) (x2 : nat) := (forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x2)) -> (real_mul (x0 y0) (real_pow x1 y0)) = (real_of_num (NUMERAL 0))) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y0 : nat => real_mul (x0 y0) (real_pow x1 y0))) = (@sum nat (dotdot (NUMERAL 0) x2) (fun y0 : nat => real_of_num (NUMERAL 0))).
Definition term125 (x0 : nat -> real) (x1 : real) (x2 : nat) := (forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x2)) -> (real_mul (x0 y0) (real_pow x1 y0)) = ((fun y1 : nat => real_of_num (NUMERAL 0)) y0)) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y0 : nat => real_mul (x0 y0) (real_pow x1 y0))) = (@sum nat (dotdot (NUMERAL 0) x2) (fun y0 : nat => real_of_num (NUMERAL 0))).
Definition term32 (x0 : nat) (x1 : nat -> real) := (fun y0 : nat -> real => (~ (forall y1 : nat, (@IN nat y1 (dotdot (NUMERAL 0) x0)) -> (y0 y1) = (real_of_num (NUMERAL 0)))) -> (@FINITE real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y3 : nat => real_mul (y0 y3) (real_pow y2 y3))) = (real_of_num (NUMERAL 0))) y2))) /\ (Peano.le (@CARD real (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y3 : nat => real_mul (y0 y3) (real_pow y2 y3))) = (real_of_num (NUMERAL 0))) y2))) x0)) x1.
Definition term23 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term58 (x0 : nat) (x1 : nat -> real) := @GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (x1 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1).
Definition term17 := @GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((fun y2 : real => True) y1) y1).
Definition term2 := @GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 True y1).
Definition term8 := fun y0 : real => True.
Definition term101 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) := fun y0 : nat => ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = (x3 y0).
Definition term122 (x0 : real) (x1 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term38 (x0 : nat) (x1 : nat -> real) := ~ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0))).
Definition term18 (x0 : real) := @IN real x0 (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 True y1)).
Definition term6 (x0 : real) := @IN real x0 (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((fun y2 : real => True) y1) y1)).
Definition term5 (x0 : real) (x1 : real -> Prop) := @IN real x0 (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 (x1 y1) y1)).
Definition term20 (x0 : real) := @eq Prop (@IN real x0 (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 True y1))).
Definition term19 (x0 : real) := @eq Prop (@IN real x0 (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((fun y2 : real => True) y1) y1))).
Definition term3 := forall y0 : real, (@IN real y0 (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 True y2))) = (@IN real y0 (@UNIV real)).
Definition term9 (x0 : real) (x1 : real) := @SETSPEC real x0 ((fun y0 : real => True) x1).
Definition term42 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0)))) x1.
Definition term22 := forall y0 : real, True.
Definition term94 (x0 : nat -> real) (x1 : real) (x2 : nat) := real_mul (x0 x2) (real_pow x1 x2).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term53 (x0 : nat) (x1 : nat -> real) := @FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (x1 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1)).
Definition term51 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term110 (x0 : nat) (x1 : nat -> real) := @sum nat (dotdot (NUMERAL 0) x0) x1.
Definition term12 (x0 : real) := fun y0 : real => @SETSPEC real x0 True y0.
Definition term24 (x0 : Prop) := forall y0 : real, x0.
Definition term43 (x0 : Prop) (x1 : Prop) := ((~ (x0 /\ x1)) = ((~ x0) \/ (~ x1))) /\ ((~ (x0 \/ x1)) = ((~ x0) /\ (~ x1))).
Definition term52 (x0 : nat -> real) (x1 : nat) := (~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (x0 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1)))) \/ (~ (Peano.le (@CARD real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (x0 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1))) x1)).
Definition term40 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (y0 /\ y1)) = ((~ y0) \/ (~ y1))) /\ ((~ (y0 \/ y1)) = ((~ y0) /\ (~ y1)))) x0.
Definition term50 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term130 (x0 : nat) (x1 : nat -> real) (x2 : real) := fun y0 : nat => ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = (real_of_num (NUMERAL 0)).
Definition term41 (x0 : Prop) := forall y0 : Prop, ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0))).
Definition term59 (x0 : nat) (x1 : nat -> real) (x2 : real) := @eq real (@sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_mul (x1 y0) (real_pow x2 y0))).
Definition term73 (x0 : nat) := True \/ (~ (Peano.le (@CARD real (@UNIV real)) x0)).
Definition term48 (x0 : nat -> real) (x1 : nat) := ((@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (x0 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1))) /\ (Peano.le (@CARD real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (x0 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1))) x1)) -> False.
Definition term92 (x0 : nat -> real) (x1 : real) := fun y0 : nat => real_mul (x0 y0) (real_pow x1 y0).
Definition term81 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0))) x1.
Definition term119 (x0 : nat) := and (Peano.le (NUMERAL 0) x0).
Definition term97 (x0 : nat) (x1 : nat) := imp ((Peano.le (NUMERAL 0) x0) /\ (Peano.le x0 x1)).
Definition term55 (x0 : real -> Prop) := ~ (@FINITE real x0).
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term13 (x0 : real) := exists y0 : real, @SETSPEC real x0 ((fun y1 : real => True) y0) y0.
Definition term14 (x0 : real) := exists y0 : real, @SETSPEC real x0 True y0.
Definition term39 (x0 : nat -> real) (x1 : nat) := (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (x0 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1))) /\ (Peano.le (@CARD real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (x0 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1))) x1).
Definition term49 (x0 : nat -> real) (x1 : nat) := ~ ((@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (x0 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1))) /\ (Peano.le (@CARD real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (x0 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1))) x1)).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term136 (x0 : nat -> Prop) := @sum nat x0 (fun y0 : nat => real_of_num (NUMERAL 0)).
Definition term142 (x0 : nat) := forall y0 : nat -> real, (forall y1 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) = (forall y1 : nat, (@IN nat y1 (dotdot (NUMERAL 0) x0)) -> (y0 y1) = (real_of_num (NUMERAL 0))).
Definition term100 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) := fun y0 : nat => ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x0)) -> ((fun y1 : nat => real_mul (x1 y1) (real_pow x2 y1)) y0) = (x3 y0).
Definition term133 (x0 : nat) (x1 : nat -> real) (x2 : real) := imp (forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = (real_of_num (NUMERAL 0))).
Definition term132 (x0 : nat) (x1 : nat -> real) (x2 : real) := imp (forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = ((fun y1 : nat => real_of_num (NUMERAL 0)) y0)).
Definition term105 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) := imp (forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = (x3 y0)).
Definition term104 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) := imp (forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x0)) -> ((fun y1 : nat => real_mul (x1 y1) (real_pow x2 y1)) y0) = (x3 y0)).
Definition term60 := @eq real (real_of_num (NUMERAL 0)).
Definition term109 (x0 : nat) (x1 : nat -> real) (x2 : real) := @eq real (@sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => (fun y1 : nat => real_mul (x1 y1) (real_pow x2 y1)) y0)).
Definition term106 (x0 : nat -> real) (x1 : real) := fun y0 : nat => (fun y1 : nat => real_mul (x0 y1) (real_pow x1 y1)) y0.
Definition term45 (x0 : nat) (x1 : nat -> real) (x2 : real) := (fun y0 : real => (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) x2.
Definition term54 (x0 : nat -> real) (x1 : nat) := Peano.le (@CARD real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (x0 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1))) x1.
Definition term75 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@sum a0 y0 (fun y1 : a0 => real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) x0.
Definition term138 (x0 : nat) (x1 : nat -> real) := fun y0 : real => (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0)).
Definition term11 (x0 : real) := fun y0 : real => @SETSPEC real x0 ((fun y1 : real => True) y0) y0.
Definition term143 := forall y0 : nat, forall y1 : nat -> real, (forall y2 : real, (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))) = (real_of_num (NUMERAL 0))) = (forall y2 : nat, (@IN nat y2 (dotdot (NUMERAL 0) y0)) -> (y1 y2) = (real_of_num (NUMERAL 0))).
Definition term80 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0)).
Definition term62 (x0 : real) (x1 : nat) (x2 : nat -> real) (x3 : real) := @SETSPEC real x0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y0 : nat => real_mul (x2 y0) (real_pow x3 y0))) = (real_of_num (NUMERAL 0))) x3.
Definition term68 (x0 : nat) (x1 : nat -> real) := Peano.le (@CARD real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (x1 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1))).
Definition term21 := fun y0 : real => (@IN real y0 (@GSPEC real (fun y1 : real => exists y2 : real, @SETSPEC real y1 True y2))) = (@IN real y0 (@UNIV real)).
Definition term134 (x0 : nat) := @sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_of_num (NUMERAL 0)).
Definition term131 (x0 : nat) (x1 : nat -> real) (x2 : real) := forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = ((fun y1 : nat => real_of_num (NUMERAL 0)) y0).
Definition term128 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat) := ((Peano.le (NUMERAL 0) x3) /\ (Peano.le x3 x0)) -> (real_mul (x1 x3) (real_pow x2 x3)) = ((fun y0 : nat => real_of_num (NUMERAL 0)) x3).
Definition term118 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term7 (x0 : real) := (fun y0 : real => True) x0.
Definition term65 (x0 : nat) (x1 : nat -> real) := fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (x1 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1.
Definition term15 := fun y0 : real => exists y1 : real, @SETSPEC real y0 ((fun y2 : real => True) y1) y1.
Definition term95 (x0 : nat -> real) (x1 : real) (x2 : nat) := @eq real ((fun y0 : nat => real_mul (x0 y0) (real_pow x1 y0)) x2).
Definition term82 (x0 : nat) (x1 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term137 (x0 : nat) := dotdot (NUMERAL 0) x0.
Definition term37 (x0 : nat) (x1 : nat -> real) := ~ (~ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0)))).
Definition term86 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (fun y0 : nat => (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0))) x2.
Definition term74 (x0 : nat) (x1 : nat -> real) := (~ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0)))) -> False.
Definition term99 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) (x4 : nat) := ((Peano.le (NUMERAL 0) x4) /\ (Peano.le x4 x0)) -> (real_mul (x1 x4) (real_pow x2 x4)) = (x3 x4).
Definition term139 (x0 : nat) (x1 : nat -> real) := (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0))) -> forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0)).
Definition term77 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term123 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat) := ((Peano.le (NUMERAL 0) x3) /\ (Peano.le x3 x0)) -> (real_mul (x1 x3) (real_pow x2 x3)) = (real_of_num (NUMERAL 0)).
Definition term35 (x0 : nat) (x1 : nat -> real) := forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0)).
Definition term72 (x0 : nat) := ~ (Peano.le (@CARD real (@UNIV real)) x0).
Definition term121 := real_mul (real_of_num (NUMERAL 0)).
Definition term28 (a0 : Type') := forall y0 : a0 -> Prop, (@INFINITE a0 y0) = (~ (@FINITE a0 y0)).
Definition term114 (x0 : nat -> real) (x1 : real) (x2 : nat) := fun y0 : nat -> real => (forall y1 : nat, ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 x2)) -> (real_mul (x0 y1) (real_pow x1 y1)) = (y0 y1)) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y1 : nat => real_mul (x0 y1) (real_pow x1 y1))) = (@sum nat (dotdot (NUMERAL 0) x2) y0).
Definition term113 (x0 : nat -> real) (x1 : real) (x2 : nat) := fun y0 : nat -> real => (forall y1 : nat, ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 x2)) -> ((fun y2 : nat => real_mul (x0 y2) (real_pow x1 y2)) y1) = (y0 y1)) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y1 : nat => (fun y2 : nat => real_mul (x0 y2) (real_pow x1 y2)) y1)) = (@sum nat (dotdot (NUMERAL 0) x2) y0).
Definition term127 (x0 : nat) := (fun y0 : nat => real_of_num (NUMERAL 0)) x0.
Definition term69 := Peano.le (@CARD real (@UNIV real)).
Definition term98 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) (x4 : nat) := ((Peano.le (NUMERAL 0) x4) /\ (Peano.le x4 x0)) -> ((fun y0 : nat => real_mul (x1 y0) (real_pow x2 y0)) x4) = (x3 x4).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) := @sum a0 x0 (fun y0 : a0 => real_of_num (NUMERAL 0)).
Definition term27 (a0 : Type') := fun y0 : a0 -> Prop => (~ (@FINITE a0 y0)) = (@INFINITE a0 y0).
Definition term57 (x0 : nat) (x1 : nat -> real) := @INFINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (x1 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1)).
Definition term26 (a0 : Type') := fun y0 : a0 -> Prop => (@INFINITE a0 y0) = (~ (@FINITE a0 y0)).
Definition term71 (x0 : nat -> real) (x1 : nat) := ~ (Peano.le (@CARD real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (x0 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1))) x1).
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1))) x2.
Definition term108 (x0 : nat) (x1 : nat -> real) (x2 : real) := @sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => (fun y1 : nat => real_mul (x1 y1) (real_pow x2 y1)) y0).
Definition term64 (x0 : real) (x1 : nat) (x2 : nat -> real) := exists y0 : real, @SETSPEC real x0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y1 : nat => real_mul (x2 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) y0.
Definition term78 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term66 (x0 : nat) (x1 : nat -> real) := or (~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (x1 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1)))).
Definition term103 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) := forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = (x3 y0).
Definition term102 (x0 : nat) (x1 : nat -> real) (x2 : real) (x3 : nat -> real) := forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x0)) -> ((fun y1 : nat => real_mul (x1 y1) (real_pow x2 y1)) y0) = (x3 y0).
Definition term96 (x0 : nat -> real) (x1 : real) (x2 : nat) := @eq real (real_mul (x0 x2) (real_pow x1 x2)).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (@FINITE a0 y0)) = (@INFINITE a0 y0)) x0.
Definition term115 (x0 : nat -> real) (x1 : real) (x2 : nat) := forall y0 : nat -> real, (forall y1 : nat, ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 x2)) -> (real_mul (x0 y1) (real_pow x1 y1)) = (y0 y1)) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y1 : nat => real_mul (x0 y1) (real_pow x1 y1))) = (@sum nat (dotdot (NUMERAL 0) x2) y0).
Definition term91 (x0 : nat -> real) (x1 : real) (x2 : nat) := forall y0 : nat -> real, (forall y1 : nat, ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 x2)) -> ((fun y2 : nat => real_mul (x0 y2) (real_pow x1 y2)) y1) = (y0 y1)) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y1 : nat => (fun y2 : nat => real_mul (x0 y2) (real_pow x1 y2)) y1)) = (@sum nat (dotdot (NUMERAL 0) x2) y0).
Definition term90 (x0 : nat -> real) (x1 : nat) (x2 : nat) := forall y0 : nat -> real, (forall y1 : nat, ((Peano.le x1 y1) /\ (Peano.le y1 x2)) -> (x0 y1) = (y0 y1)) -> (@sum nat (dotdot x1 x2) (fun y1 : nat => x0 y1)) = (@sum nat (dotdot x1 x2) y0).
Definition term129 (x0 : nat) (x1 : nat -> real) (x2 : real) := fun y0 : nat => ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = ((fun y1 : nat => real_of_num (NUMERAL 0)) y0).
Definition term33 (x0 : nat -> real) (x1 : nat) := (~ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x1)) -> (x0 y0) = (real_of_num (NUMERAL 0)))) -> (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (x0 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1))) /\ (Peano.le (@CARD real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x1) (fun y2 : nat => real_mul (x0 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1))) x1).
Definition term88 (x0 : nat) (x1 : nat) := @IN nat x0 (dotdot (NUMERAL 0) x1).
Definition term56 (x0 : nat) (x1 : nat -> real) := ~ (@FINITE real (@GSPEC real (fun y0 : real => exists y1 : real, @SETSPEC real y0 ((@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (x1 y2) (real_pow y1 y2))) = (real_of_num (NUMERAL 0))) y1))).
Definition term46 (x0 : nat) (x1 : nat -> real) (x2 : real) := @sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_mul (x1 y0) (real_pow x2 y0)).
Definition term29 (a0 : Type') := forall y0 : a0 -> Prop, (~ (@FINITE a0 y0)) = (@INFINITE a0 y0).
Definition term116 (x0 : nat -> real) (x1 : real) (x2 : nat) (x3 : nat -> real) := (fun y0 : nat -> real => (forall y1 : nat, ((Peano.le (NUMERAL 0) y1) /\ (Peano.le y1 x2)) -> (real_mul (x0 y1) (real_pow x1 y1)) = (y0 y1)) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y1 : nat => real_mul (x0 y1) (real_pow x1 y1))) = (@sum nat (dotdot (NUMERAL 0) x2) y0)) x3.
Definition term141 (x0 : nat) (x1 : nat -> real) := ((forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) -> forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0))) /\ ((forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0))) -> forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))).
Definition term124 (x0 : nat) (x1 : nat -> real) (x2 : real) := forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x0)) -> (real_mul (x1 y0) (real_pow x2 y0)) = (real_of_num (NUMERAL 0)).
Definition term36 (x0 : nat) (x1 : nat -> real) := forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0)).
Definition term112 (x0 : nat -> real) (x1 : real) (x2 : nat) (x3 : nat -> real) := (forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x2)) -> (real_mul (x0 y0) (real_pow x1 y0)) = (x3 y0)) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y0 : nat => real_mul (x0 y0) (real_pow x1 y0))) = (@sum nat (dotdot (NUMERAL 0) x2) x3).
Definition term111 (x0 : nat -> real) (x1 : real) (x2 : nat) (x3 : nat -> real) := (forall y0 : nat, ((Peano.le (NUMERAL 0) y0) /\ (Peano.le y0 x2)) -> ((fun y1 : nat => real_mul (x0 y1) (real_pow x1 y1)) y0) = (x3 y0)) -> (@sum nat (dotdot (NUMERAL 0) x2) (fun y0 : nat => (fun y1 : nat => real_mul (x0 y1) (real_pow x1 y1)) y0)) = (@sum nat (dotdot (NUMERAL 0) x2) x3).
Definition term89 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : nat -> real) := (forall y0 : nat, ((Peano.le x1 y0) /\ (Peano.le y0 x2)) -> (x0 y0) = (x3 y0)) -> (@sum nat (dotdot x1 x2) (fun y0 : nat => x0 y0)) = (@sum nat (dotdot x1 x2) x3).
Definition term10 (x0 : real) (x1 : real) := @SETSPEC real x0 ((fun y0 : real => True) x1) x1.
Definition term87 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (@IN nat x2 (dotdot (NUMERAL 0) x0)) -> (x1 x2) = (real_of_num (NUMERAL 0)).
Definition term140 (x0 : nat) (x1 : nat -> real) := (forall y0 : real, (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))) = (real_of_num (NUMERAL 0))) -> forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL 0) x0)) -> (x1 y0) = (real_of_num (NUMERAL 0)).
Definition term1 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (@IN real y0 x0) = (@IN real y0 x1).
