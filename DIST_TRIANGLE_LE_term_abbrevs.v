Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2)).
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, Peano.le (dist (@pair nat nat y0 y2)) (Nat.add (dist (@pair nat nat y0 y1)) (dist (@pair nat nat y1 y2)))) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term14 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term8 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term19 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 x1).
Definition term12 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le (dist (@pair nat nat x0 y0)) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 y0)))) x2.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term22 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le (dist (@pair nat nat x0 y1)) (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 y1)))) x1.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat x0 x2)) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2))).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := and (Peano.le (dist (@pair nat nat x0 x2)) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2)))).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 x2))) x3) -> Peano.le (dist (@pair nat nat x1 x2)) x3.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2))) x3.
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (Peano.le (dist (@pair nat nat x0 x1)) y0) /\ (Peano.le y0 x2).
Definition term36 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le (Nat.add (dist (@pair nat nat y0 y1)) (dist (@pair nat nat y1 y2))) y3) -> Peano.le (dist (@pair nat nat y0 y2)) y3.
Definition term35 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 y1))) y2) -> Peano.le (dist (@pair nat nat x0 y1)) y2.
Definition term34 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 y0))) y1) -> Peano.le (dist (@pair nat nat x1 y0)) y1.
Definition term21 (x0 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat x0 y1)) (Nat.add (dist (@pair nat nat x0 y0)) (dist (@pair nat nat y0 y1))).
Definition term13 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term2 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le (dist (@pair nat nat x0 x2)) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2)))) /\ (Peano.le (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2))) x3).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (Peano.le (dist (@pair nat nat x0 x1)) y0) /\ (Peano.le y0 x2)) -> Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (Peano.le (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 x2))) y0) -> Peano.le (dist (@pair nat nat x1 x2)) y0.
Definition term11 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term10 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat x0 x1)) x2.
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (Peano.le (dist (@pair nat nat x0 x1)) y0) /\ (Peano.le y0 x2).
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term23 (x0 : nat) (x1 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat x0 y0)) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 y0))).
