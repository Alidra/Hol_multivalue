Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 ((fun y3 : nat => NUMERAL 0) y2)) (Nat.mul y2 ((fun y3 : nat => NUMERAL 0) y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term9 (x0 : nat -> nat) := exists y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 (x0 y2)) (Nat.mul y2 (x0 y1)))) (Nat.mul y0 (Nat.add y1 y2)).
Definition term36 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term16 (x0 : nat) := (fun y0 : nat => NUMERAL 0) x0.
Definition term32 (x0 : nat) (x1 : nat) := fun y0 : nat => Peano.le (dist (@pair nat nat (Nat.mul x1 ((fun y1 : nat => NUMERAL 0) y0)) (Nat.mul y0 ((fun y1 : nat => NUMERAL 0) x1)))) (Nat.mul x0 (Nat.add x1 y0)).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (NUMERAL 0) (Nat.mul x0 (Nat.add x1 x2)).
Definition term41 := exists y0 : nat, True.
Definition term10 := is_nadd (fun y0 : nat => NUMERAL 0).
Definition term12 := fun y0 : nat => NUMERAL 0.
Definition term21 (x0 : nat) (x1 : nat) := @pair nat nat (Nat.mul x0 ((fun y0 : nat => NUMERAL 0) x1)).
Definition term6 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term20 (x0 : nat) (x1 : nat) := Nat.mul x0 ((fun y0 : nat => NUMERAL 0) x1).
Definition term43 (x0 : Prop) := exists y0 : nat, x0.
Definition term34 (x0 : nat) (x1 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat (Nat.mul x1 ((fun y1 : nat => NUMERAL 0) y0)) (Nat.mul y0 ((fun y1 : nat => NUMERAL 0) x1)))) (Nat.mul x0 (Nat.add x1 y0)).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term39 (x0 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 ((fun y2 : nat => NUMERAL 0) y1)) (Nat.mul y1 ((fun y2 : nat => NUMERAL 0) y0)))) (Nat.mul x0 (Nat.add y0 y1)).
Definition term8 (x0 : nat -> nat) := (fun y0 : nat -> nat => (is_nadd y0) = (exists y1 : nat, forall y2 : nat, forall y3 : nat, Peano.le (dist (@pair nat nat (Nat.mul y2 (y0 y3)) (Nat.mul y3 (y0 y2)))) (Nat.mul y1 (Nat.add y2 y3)))) x0.
Definition term3 (x0 : nat) := dist (@pair nat nat x0 x0).
Definition term14 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term35 := forall y0 : nat, True.
Definition term22 := @pair nat nat (NUMERAL 0).
Definition term1 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x1 ((fun y0 : nat => NUMERAL 0) x2)) (Nat.mul x2 ((fun y0 : nat => NUMERAL 0) x1)))) (Nat.mul x0 (Nat.add x1 x2)).
Definition term33 := fun y0 : nat => True.
Definition term17 := fun y0 : nat => (fun y1 : nat => NUMERAL 0) y0.
Definition term25 (x0 : nat) (x1 : nat) := dist (@pair nat nat (Nat.mul x1 ((fun y0 : nat => NUMERAL 0) x0)) (Nat.mul x0 ((fun y0 : nat => NUMERAL 0) x1))).
Definition term42 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term24 := @pair nat nat (NUMERAL 0) (NUMERAL 0).
Definition term19 (x0 : nat) := @eq nat ((fun y0 : nat => NUMERAL 0) x0).
Definition term18 (x0 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => NUMERAL 0) y0) x0).
Definition term5 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term23 (x0 : nat) (x1 : nat) := @pair nat nat (Nat.mul x1 ((fun y0 : nat => NUMERAL 0) x0)) (Nat.mul x0 ((fun y0 : nat => NUMERAL 0) x1)).
Definition term7 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term37 (x0 : Prop) := forall y0 : nat, x0.
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term26 := dist (@pair nat nat (NUMERAL 0) (NUMERAL 0)).
Definition term28 := Peano.le (NUMERAL 0).
Definition term2 (x0 : nat) := (fun y0 : nat => (dist (@pair nat nat y0 y0)) = (NUMERAL 0)) x0.
Definition term15 (x0 : nat) := (fun y0 : nat => (fun y1 : nat => NUMERAL 0) y0) x0.
Definition term4 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term27 (x0 : nat) (x1 : nat) := Peano.le (dist (@pair nat nat (Nat.mul x1 ((fun y0 : nat => NUMERAL 0) x0)) (Nat.mul x0 ((fun y0 : nat => NUMERAL 0) x1)))).
Definition term38 (x0 : nat) := fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat (Nat.mul y0 ((fun y2 : nat => NUMERAL 0) y1)) (Nat.mul y1 ((fun y2 : nat => NUMERAL 0) y0)))) (Nat.mul x0 (Nat.add y0 y1)).
Definition term40 := fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat (Nat.mul y1 ((fun y3 : nat => NUMERAL 0) y2)) (Nat.mul y2 ((fun y3 : nat => NUMERAL 0) y1)))) (Nat.mul y0 (Nat.add y1 y2)).
