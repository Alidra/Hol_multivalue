Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := imp ((Nat.add x1 x0) = (Nat.add (Nat.add (Nat.add x1 x2) x3) x4)).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (((Nat.add (Nat.add x0 x1) x2) = (Nat.add (Nat.add x0 x3) x4)) -> (fun y0 : nat => Peano.le x1 (Nat.add y0 (dist (@pair nat nat x2 x3)))) x4) /\ (((Nat.add x0 x3) = (Nat.add (Nat.add (Nat.add x0 x1) x2) x4)) -> (fun y0 : nat => Peano.le x1 (Nat.add y0 (dist (@pair nat nat x2 x3)))) x4).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((Nat.add (Nat.add x0 x1) x3) = (Nat.add (Nat.add x0 x4) x2)) -> Peano.le x1 (Nat.add x2 (dist (@pair nat nat x3 x4))).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((Nat.add x0 x4) = (Nat.add (Nat.add (Nat.add x0 x1) x3) x2)) -> Peano.le x1 (Nat.add x2 (dist (@pair nat nat x3 x4))).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (Peano.le x0 (Nat.add (dist (@pair nat nat (Nat.add (Nat.add x1 x0) x2) (Nat.add x1 x3))) (dist (@pair nat nat x2 x3)))).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (((Nat.add (Nat.add x0 x1) x3) = (Nat.add (Nat.add x0 x4) x2)) -> Peano.le x1 (Nat.add x2 (dist (@pair nat nat x3 x4)))) /\ (((Nat.add x0 x4) = (Nat.add (Nat.add (Nat.add x0 x1) x3) x2)) -> Peano.le x1 (Nat.add x2 (dist (@pair nat nat x3 x4)))).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => (((Nat.add (Nat.add x0 x1) x2) = (Nat.add (Nat.add x0 x3) y0)) -> (fun y1 : nat => Peano.le x1 (Nat.add y1 (dist (@pair nat nat x2 x3)))) y0) /\ (((Nat.add x0 x3) = (Nat.add (Nat.add (Nat.add x0 x1) x2) y0)) -> (fun y1 : nat => Peano.le x1 (Nat.add y1 (dist (@pair nat nat x2 x3)))) y0).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := imp ((Nat.add (Nat.add x2 x0) x1) = (Nat.add (Nat.add x2 x3) x4)).
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le x0 (Nat.add y0 (dist (@pair nat nat x1 x2))).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add y0 (dist (@pair nat nat x1 x2)))) x3.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((Nat.add (Nat.add x0 x1) x2) = (Nat.add (Nat.add x0 x3) x4)) -> (fun y0 : nat => Peano.le x1 (Nat.add y0 (dist (@pair nat nat x2 x3)))) x4.
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((Nat.add x0 x3) = (Nat.add (Nat.add (Nat.add x0 x1) x2) x4)) -> (fun y0 : nat => Peano.le x1 (Nat.add y0 (dist (@pair nat nat x2 x3)))) x4.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add y0 (dist (@pair nat nat x1 x2)))) (dist (@pair nat nat x3 x4)).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((fun y0 : nat => Peano.le x0 (Nat.add y0 (dist (@pair nat nat x1 x3)))) (dist (@pair nat nat (Nat.add (Nat.add x2 x0) x1) (Nat.add x2 x3)))).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le x0 (Nat.add x1 (dist (@pair nat nat x2 x3))).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le x0 (Nat.add (dist (@pair nat nat (Nat.add (Nat.add x1 x0) x2) (Nat.add x1 x3))) (dist (@pair nat nat x2 x3))).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, (((Nat.add (Nat.add x0 x1) x2) = (Nat.add (Nat.add x0 x3) y0)) -> (fun y1 : nat => Peano.le x1 (Nat.add y1 (dist (@pair nat nat x2 x3)))) y0) /\ (((Nat.add x0 x3) = (Nat.add (Nat.add (Nat.add x0 x1) x2) y0)) -> (fun y1 : nat => Peano.le x1 (Nat.add y1 (dist (@pair nat nat x2 x3)))) y0).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := forall y0 : nat, ((x1 = (Nat.add x0 y0)) -> (fun y1 : nat => Peano.le x2 (Nat.add y1 (dist (@pair nat nat x3 x4)))) y0) /\ ((x0 = (Nat.add x1 y0)) -> (fun y1 : nat => Peano.le x2 (Nat.add y1 (dist (@pair nat nat x3 x4)))) y0).
Definition term3 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add y0 (dist (@pair nat nat x1 x3)))) (dist (@pair nat nat (Nat.add (Nat.add x2 x0) x1) (Nat.add x2 x3))).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => (((Nat.add (Nat.add x0 x1) x2) = (Nat.add (Nat.add x0 x3) y0)) -> Peano.le x1 (Nat.add y0 (dist (@pair nat nat x2 x3)))) /\ (((Nat.add x0 x3) = (Nat.add (Nat.add (Nat.add x0 x1) x2) y0)) -> Peano.le x1 (Nat.add y0 (dist (@pair nat nat x2 x3)))).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := and (((Nat.add (Nat.add x0 x1) x2) = (Nat.add (Nat.add x0 x3) x4)) -> (fun y0 : nat => Peano.le x1 (Nat.add y0 (dist (@pair nat nat x2 x3)))) x4).
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, (((Nat.add (Nat.add x0 x1) x2) = (Nat.add (Nat.add x0 x3) y0)) -> Peano.le x1 (Nat.add y0 (dist (@pair nat nat x2 x3)))) /\ (((Nat.add x0 x3) = (Nat.add (Nat.add (Nat.add x0 x1) x2) y0)) -> Peano.le x1 (Nat.add y0 (dist (@pair nat nat x2 x3)))).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := and (((Nat.add (Nat.add x0 x1) x3) = (Nat.add (Nat.add x0 x4) x2)) -> Peano.le x1 (Nat.add x2 (dist (@pair nat nat x3 x4)))).