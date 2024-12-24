Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => Peano.le x0 (Nat.add (dist (@pair nat nat (Nat.add y0 x2) (Nat.add x1 x3))) (dist (@pair nat nat x2 x3))).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := @eq Prop (Peano.le x0 (Nat.add (dist (@pair nat nat (Nat.add x1 x3) (Nat.add x2 x4))) (dist (@pair nat nat x3 x4)))).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add (dist (@pair nat nat (Nat.add y0 x2) (Nat.add x1 x3))) (dist (@pair nat nat x2 x3)))) x4.
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := @eq Prop ((fun y0 : nat => Peano.le x0 (Nat.add (dist (@pair nat nat (Nat.add y0 x2) (Nat.add x1 x3))) (dist (@pair nat nat x2 x3)))) x4).
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le x3 (Nat.add (dist (@pair nat nat (Nat.add y0 x0) (Nat.add x2 x1))) (dist (@pair nat nat x0 x1)))) (Nat.add x2 x3).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := Peano.le x0 (Nat.add (dist (@pair nat nat (Nat.add x1 x3) (Nat.add x2 x4))) (dist (@pair nat nat x3 x4))).
Definition term3 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le x0 (Nat.add (dist (@pair nat nat (Nat.add (Nat.add x1 x0) x2) (Nat.add x1 x3))) (dist (@pair nat nat x2 x3))).
