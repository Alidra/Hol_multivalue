Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((fun y0 : nat => Peano.le x2 (Nat.add x0 (dist (@pair nat nat x1 (Nat.add y0 x2))))) x3).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le x3 (Nat.add x0 (dist (@pair nat nat x1 (Nat.add x2 x3)))).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => Peano.le x2 (Nat.add x0 (dist (@pair nat nat x1 (Nat.add y0 x2)))).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le x2 (Nat.add x0 (dist (@pair nat nat x1 (Nat.add y0 x2))))) x3.
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x2 (dist (@pair nat nat x1 (Nat.add y0 x0))))) (Nat.add x1 x2).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (Peano.le x3 (Nat.add x0 (dist (@pair nat nat x1 (Nat.add x2 x3))))).
Definition term3 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x2 (Nat.add x1 (dist (@pair nat nat x0 (Nat.add (Nat.add x0 x1) x2)))).
