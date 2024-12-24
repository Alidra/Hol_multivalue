Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term36 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.sub x0 x1) x1).
Definition term9 (x0 : nat) := fun y0 : nat => (Nat.sub (Nat.add y0 x0) y0) = x0.
Definition term8 (x0 : nat) := fun y0 : nat => (Nat.sub (Nat.add x0 y0) y0) = x0.
Definition term37 (x0 : nat) (x1 : nat) := @eq nat (Nat.add x0 x1).
Definition term26 (x0 : nat) := fun y0 : nat => (exists y1 : nat, x0 = (Nat.add y0 y1)) -> (Nat.add (Nat.sub x0 y0) y0) = x0.
Definition term38 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term28 (x0 : nat) := forall y0 : nat, (exists y1 : nat, x0 = (Nat.add y0 y1)) -> (Nat.add (Nat.sub x0 y0) y0) = x0.
Definition term17 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term24 (x0 : nat) (x1 : nat) := (exists y0 : nat, x1 = (Nat.add x0 y0)) -> (Nat.add (Nat.sub x1 x0) x0) = x1.
Definition term20 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term11 (x0 : nat) := forall y0 : nat, (Nat.sub (Nat.add y0 x0) y0) = x0.
Definition term10 (x0 : nat) := forall y0 : nat, (Nat.sub (Nat.add x0 y0) y0) = x0.
Definition term35 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub x0 x1).
Definition term33 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add y1 y0) y1) = y0) x0.
Definition term21 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term34 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (Nat.add y0 x0) y0) = x0) x1.
Definition term30 := fun y0 : nat => forall y1 : nat, (exists y2 : nat, y0 = (Nat.add y1 y2)) -> (Nat.add (Nat.sub y0 y1) y1) = y0.
Definition term29 := fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0.
Definition term25 (x0 : nat) := fun y0 : nat => (Peano.le y0 x0) -> (Nat.add (Nat.sub x0 y0) y0) = x0.
Definition term19 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term5 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x1 x0) x1.
Definition term32 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, y0 = (Nat.add y1 y2)) -> (Nat.add (Nat.sub y0 y1) y1) = y0.
Definition term31 := forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) -> (Nat.add (Nat.sub y0 y1) y1) = y0.
Definition term15 := forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add y1 y0) y1) = y0.
Definition term14 := forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add y0 y1) y1) = y0.
Definition term7 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (Nat.add x1 x0) x1).
Definition term6 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (Nat.add x0 x1) x1).
Definition term1 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term13 := fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add y1 y0) y1) = y0.
Definition term12 := fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add y0 y1) y1) = y0.
Definition term3 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x0 x1).
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term22 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub x0 x1) x1.
Definition term23 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> (Nat.add (Nat.sub x1 x0) x0) = x1.
Definition term18 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term4 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x0 x1) x1.
Definition term27 (x0 : nat) := forall y0 : nat, (Peano.le y0 x0) -> (Nat.add (Nat.sub x0 y0) y0) = x0.
