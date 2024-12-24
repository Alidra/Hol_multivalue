Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.sub (Nat.add x1 x0) (Nat.add x1 x2)).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.sub (Nat.add x0 x1) (Nat.add x0 y0)) = (Nat.sub x1 y0)) x2.
Definition term11 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.sub (Nat.add y0 x0) (Nat.add y0 x1)) = (Nat.sub x0 x1).
Definition term10 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.sub (Nat.add x0 y0) (Nat.add x1 y0)) = (Nat.sub x0 x1).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.sub (Nat.add x0 x2) (Nat.add x1 x2)).
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y1) (Nat.add y0 y2)) = (Nat.sub y1 y2)) x0.
Definition term23 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.sub (Nat.add x0 x1) (Nat.add x0 y0)) = (Nat.sub x1 y0).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.sub (Nat.add x0 x2) (Nat.add x1 x2).
Definition term22 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add x0 y0) (Nat.add x0 y1)) = (Nat.sub y0 y1)) x1.
Definition term13 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add y1 x0) (Nat.add y1 y0)) = (Nat.sub x0 y0).
Definition term12 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add x0 y1) (Nat.add y0 y1)) = (Nat.sub x0 y0).
Definition term21 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add x0 y0) (Nat.add x0 y1)) = (Nat.sub y0 y1).
Definition term19 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y2 y0) (Nat.add y2 y1)) = (Nat.sub y0 y1).
Definition term18 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y2) (Nat.add y1 y2)) = (Nat.sub y0 y1).
Definition term15 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add y1 x0) (Nat.add y1 y0)) = (Nat.sub x0 y0).
Definition term14 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.sub (Nat.add x0 y1) (Nat.add y0 y1)) = (Nat.sub x0 y0).
Definition term1 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term9 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.sub (Nat.add y0 x0) (Nat.add y0 x1)) = (Nat.sub x0 x1).
Definition term8 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.sub (Nat.add x0 y0) (Nat.add x1 y0)) = (Nat.sub x0 x1).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term3 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x0 x1).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.sub (Nat.add x1 x0) (Nat.add x1 x2).
Definition term17 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y2 y0) (Nat.add y2 y1)) = (Nat.sub y0 y1).
Definition term16 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.sub (Nat.add y0 y2) (Nat.add y1 y2)) = (Nat.sub y0 y1).
