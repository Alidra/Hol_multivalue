Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 := fun y0 : nat => forall y1 : nat, (Nat.sub y1 (Nat.add y1 y0)) = (NUMERAL 0).
Definition term11 := fun y0 : nat => forall y1 : nat, (Nat.sub y1 (Nat.add y0 y1)) = (NUMERAL 0).
Definition term14 := forall y0 : nat, forall y1 : nat, (Nat.sub y1 (Nat.add y1 y0)) = (NUMERAL 0).
Definition term13 := forall y0 : nat, forall y1 : nat, (Nat.sub y1 (Nat.add y0 y1)) = (NUMERAL 0).
Definition term8 (x0 : nat) := fun y0 : nat => (Nat.sub y0 (Nat.add y0 x0)) = (NUMERAL 0).
Definition term7 (x0 : nat) := fun y0 : nat => (Nat.sub y0 (Nat.add x0 y0)) = (NUMERAL 0).
Definition term17 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub x0 (Nat.add x0 y0)) = (NUMERAL 0)) x1.
Definition term1 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term5 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub x1 (Nat.add x0 x1)).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term6 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub x0 (Nat.add x0 x1)).
Definition term4 (x0 : nat) (x1 : nat) := Nat.sub x0 (Nat.add x0 x1).
Definition term15 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub y0 (Nat.add y0 y1)) = (NUMERAL 0)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term16 (x0 : nat) := forall y0 : nat, (Nat.sub x0 (Nat.add x0 y0)) = (NUMERAL 0).
Definition term10 (x0 : nat) := forall y0 : nat, (Nat.sub y0 (Nat.add y0 x0)) = (NUMERAL 0).
Definition term9 (x0 : nat) := forall y0 : nat, (Nat.sub y0 (Nat.add x0 y0)) = (NUMERAL 0).
Definition term3 (x0 : nat) (x1 : nat) := Nat.sub x1 (Nat.add x0 x1).
