Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.sub x0 x1) x2).
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.sub y0 y1) y2) = (Nat.sub (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add (Nat.sub x1 x0) (Nat.sub x0 x1)) x2.
Definition term34 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term17 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 x1).
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.sub x0 y0) y1) = (Nat.sub (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.sub x0 x1) x2.
Definition term39 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.mul (dist (@pair nat nat y0 y1)) y2) = (dist (@pair nat nat (Nat.mul y0 y2) (Nat.mul y1 y2))).
Definition term37 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (dist (@pair nat nat x0 y0)) y1) = (dist (@pair nat nat (Nat.mul x0 y1) (Nat.mul y0 y1))).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.sub x0 y0) y1) = (Nat.sub (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.sub x0 x1) y0) = (Nat.sub (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term30 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.mul (dist (@pair nat nat x0 x1)) y0) = (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x1 y0))).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term33 := forall y0 : nat, True.
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.sub x1 x0) x2) (Nat.mul (Nat.sub x0 x1) x2).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term31 := fun y0 : nat => True.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.sub (Nat.mul x0 x2) (Nat.mul x1 x2)).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.sub (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.mul (dist (@pair nat nat x0 x1)) x2).
Definition term32 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (dist (@pair nat nat x0 x1)) y0) = (dist (@pair nat nat (Nat.mul x0 y0) (Nat.mul x1 y0))).
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat y1 y0)) = (Nat.add (Nat.sub y1 y0) (Nat.sub y0 y1))) x0.
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.sub (Nat.mul x1 x2) (Nat.mul x0 x2)) (Nat.sub (Nat.mul x0 x2) (Nat.mul x1 x2)).
Definition term20 (x0 : nat) (x1 : nat) := Nat.mul (Nat.add (Nat.sub x1 x0) (Nat.sub x0 x1)).
Definition term10 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.sub x0 x1) y0) = (Nat.sub (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term18 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub x1 x0) (Nat.sub x0 x1).
Definition term35 (x0 : Prop) := forall y0 : nat, x0.
Definition term36 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.mul (dist (@pair nat nat x0 y0)) y1) = (dist (@pair nat nat (Nat.mul x0 y1) (Nat.mul y0 y1))).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := dist (@pair nat nat (Nat.mul x0 x2) (Nat.mul x1 x2)).
Definition term15 (x0 : nat) := forall y0 : nat, (dist (@pair nat nat y0 x0)) = (Nat.add (Nat.sub y0 x0) (Nat.sub x0 y0)).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (dist (@pair nat nat x0 x1)) x2.
Definition term19 (x0 : nat) (x1 : nat) := Nat.mul (dist (@pair nat nat x0 x1)).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.sub (Nat.mul x1 x2) (Nat.mul x0 x2)) (Nat.sub (Nat.mul x0 x2) (Nat.mul x1 x2))).
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dist (@pair nat nat y0 x0)) = (Nat.add (Nat.sub y0 x0) (Nat.sub x0 y0))) x1.
Definition term38 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (dist (@pair nat nat y0 y1)) y2) = (dist (@pair nat nat (Nat.mul y0 y2) (Nat.mul y1 y2))).
