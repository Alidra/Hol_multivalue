Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.add (Nat.add x0 x1) x2) x3)) -> Peano.le x1 (Nat.add x2 x3).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.add (Nat.add x0 x2) x1) x3)) -> Peano.le x1 (Nat.add x2 x3).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.add x1 x2).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x1 = (Nat.add x3 x0)) -> Peano.le x0 (Nat.add (dist (@pair nat nat x1 x2)) (dist (@pair nat nat x2 x3))).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = (Nat.add (Nat.add (Nat.add x0 x2) x1) x3)) -> Peano.le x1 (Nat.add x2 x3)) /\ (((Nat.add (Nat.add x0 x2) x1) = (Nat.add x0 x3)) -> Peano.le x1 (Nat.add x2 x3)).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (((Nat.add x0 x2) = (Nat.add (Nat.add x0 x1) x3)) -> Peano.le x1 (Nat.add x2 x3)) /\ (((Nat.add x0 x1) = (Nat.add (Nat.add x0 x2) x3)) -> Peano.le x1 (Nat.add x2 x3)).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((x1 = (Nat.add x0 x4)) -> Peano.le x2 (Nat.add x3 x4)) /\ ((x0 = (Nat.add x1 x4)) -> Peano.le x2 (Nat.add x3 x4)).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le x3 (Nat.add x0 (dist (@pair nat nat x1 (Nat.add x2 x3)))).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = (Nat.add x3 x0)) -> Peano.le x0 (Nat.add (dist (@pair nat nat x1 x2)) (dist (@pair nat nat x2 x3)))) /\ ((x3 = (Nat.add x1 x0)) -> Peano.le x0 (Nat.add (dist (@pair nat nat x1 x2)) (dist (@pair nat nat x2 x3)))).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (dist (@pair nat nat x0 x2)) (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2))).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = (Nat.add x1 x0)) -> Peano.le x0 (Nat.add (dist (@pair nat nat x1 x2)) (dist (@pair nat nat x2 x3))).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (((Nat.add x3 x0) = (Nat.add x2 x1)) -> Peano.le x0 (Nat.add x1 (dist (@pair nat nat x2 x3)))) /\ ((x2 = (Nat.add (Nat.add x3 x0) x1)) -> Peano.le x0 (Nat.add x1 (dist (@pair nat nat x2 x3)))).
Definition term3 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add x0 x2) = (Nat.add (Nat.add x0 x1) x3)) -> Peano.le x1 (Nat.add x2 x3).
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add x0 x1) = (Nat.add (Nat.add x0 x2) x3)) -> Peano.le x1 (Nat.add x2 x3).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add x3 x0) = (Nat.add x2 x1)) -> Peano.le x0 (Nat.add x1 (dist (@pair nat nat x2 x3))).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = (Nat.add (Nat.add x3 x0) x1)) -> Peano.le x0 (Nat.add x1 (dist (@pair nat nat x2 x3))).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x2 = (Nat.add x1 x0)) -> Peano.le x3 (Nat.add x0 (dist (@pair nat nat x1 (Nat.add x2 x3))))) /\ ((x1 = (Nat.add x2 x0)) -> Peano.le x3 (Nat.add x0 (dist (@pair nat nat x1 (Nat.add x2 x3))))).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (x0 = (Nat.add x1 x4)) -> Peano.le x2 (Nat.add x3 x4).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (((Nat.add (Nat.add x0 x1) x2) = (Nat.add x0 x3)) -> Peano.le x1 (Nat.add x2 x3)) /\ ((x0 = (Nat.add (Nat.add (Nat.add x0 x1) x2) x3)) -> Peano.le x1 (Nat.add x2 x3)).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x1 = (Nat.add x2 x0)) -> Peano.le x3 (Nat.add x0 (dist (@pair nat nat x1 (Nat.add x2 x3)))).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le x0 (Nat.add x1 (dist (@pair nat nat x2 x3))).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.add x1 (dist (@pair nat nat (Nat.add (Nat.add x2 x0) x1) x2))).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x2 (Nat.add x0 (dist (@pair nat nat (Nat.add x1 x0) (Nat.add x1 x2)))).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le x0 (Nat.add (dist (@pair nat nat x1 x2)) (dist (@pair nat nat x2 x3))).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.add (dist (@pair nat nat (Nat.add x2 x0) x1)) (dist (@pair nat nat x1 x2))).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add (Nat.add x0 x1) x2) x3.
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add (Nat.add x0 x1) x2) = (Nat.add x0 x3)) -> Peano.le x1 (Nat.add x2 x3).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add (Nat.add x0 x2) x1) = (Nat.add x0 x3)) -> Peano.le x1 (Nat.add x2 x3).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x2 (Nat.add (dist (@pair nat nat x1 x0)) (dist (@pair nat nat x0 (Nat.add x1 x2)))).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x2 (Nat.add x1 (dist (@pair nat nat x0 (Nat.add (Nat.add x0 x1) x2)))).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = (Nat.add x1 x0)) -> Peano.le x3 (Nat.add x0 (dist (@pair nat nat x1 (Nat.add x2 x3)))).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((x0 = (Nat.add x2 y0)) -> Peano.le y0 (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2)))) /\ ((x2 = (Nat.add x0 y0)) -> Peano.le y0 (Nat.add (dist (@pair nat nat x0 x1)) (dist (@pair nat nat x1 x2)))).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (((Nat.add x2 x0) = (Nat.add x1 y0)) -> Peano.le x0 (Nat.add y0 (dist (@pair nat nat x1 x2)))) /\ ((x1 = (Nat.add (Nat.add x2 x0) y0)) -> Peano.le x0 (Nat.add y0 (dist (@pair nat nat x1 x2)))).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, ((x1 = (Nat.add x0 y0)) -> Peano.le x2 (Nat.add x3 y0)) /\ ((x0 = (Nat.add x1 y0)) -> Peano.le x2 (Nat.add x3 y0)).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (((Nat.add (Nat.add x0 x1) x2) = (Nat.add x0 y0)) -> Peano.le x1 (Nat.add x2 y0)) /\ ((x0 = (Nat.add (Nat.add (Nat.add x0 x1) x2) y0)) -> Peano.le x1 (Nat.add x2 y0)).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((x1 = (Nat.add x0 y0)) -> Peano.le x2 (Nat.add y0 (dist (@pair nat nat x0 (Nat.add x1 x2))))) /\ ((x0 = (Nat.add x1 y0)) -> Peano.le x2 (Nat.add y0 (dist (@pair nat nat x0 (Nat.add x1 x2))))).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((x0 = (Nat.add (Nat.add (Nat.add x0 x2) x1) y0)) -> Peano.le x1 (Nat.add x2 y0)) /\ (((Nat.add (Nat.add x0 x2) x1) = (Nat.add x0 y0)) -> Peano.le x1 (Nat.add x2 y0)).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (((Nat.add x0 x2) = (Nat.add (Nat.add x0 x1) y0)) -> Peano.le x1 (Nat.add x2 y0)) /\ (((Nat.add x0 x1) = (Nat.add (Nat.add x0 x2) y0)) -> Peano.le x1 (Nat.add x2 y0)).
