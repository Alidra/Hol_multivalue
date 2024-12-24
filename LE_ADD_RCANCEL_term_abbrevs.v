Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add y0 x0) (Nat.add y0 x1)) = (Peano.le x0 x1).
Definition term10 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x1 y0)) = (Peano.le x0 x1).
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y1) (Nat.add y0 y2)) = (Peano.le y1 y2)) x0.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0)) x2.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (Peano.le (Nat.add x0 x2) (Nat.add x1 x2)).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x0 x2) (Nat.add x1 x2).
Definition term9 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le (Nat.add y0 x0) (Nat.add y0 x1)) = (Peano.le x0 x1).
Definition term8 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le (Nat.add x0 y0) (Nat.add x1 y0)) = (Peano.le x0 x1).
Definition term23 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x1 x0) (Nat.add x1 x2).
Definition term22 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1)) x1.
Definition term13 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add y1 x0) (Nat.add y1 y0)) = (Peano.le x0 y0).
Definition term12 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y1) (Nat.add y0 y1)) = (Peano.le x0 y0).
Definition term3 (x0 : nat) (x1 : nat) := Peano.le (Nat.add x0 x1).
Definition term21 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1).
Definition term19 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y2 y0) (Nat.add y2 y1)) = (Peano.le y0 y1).
Definition term18 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.le y0 y1).
Definition term15 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add y1 x0) (Nat.add y1 y0)) = (Peano.le x0 y0).
Definition term14 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y1) (Nat.add y0 y1)) = (Peano.le x0 y0).
Definition term1 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (Peano.le (Nat.add x1 x0) (Nat.add x1 x2)).
Definition term17 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y2 y0) (Nat.add y2 y1)) = (Peano.le y0 y1).
Definition term16 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y2) (Nat.add y1 y2)) = (Peano.le y0 y1).
