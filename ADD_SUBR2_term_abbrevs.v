Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.sub x0 y0) = (NUMERAL 0)) = (Peano.le x0 y0)) x1.
Definition term14 := fun y0 : nat => forall y1 : nat, (Nat.sub y0 (Nat.add y0 y1)) = (NUMERAL 0).
Definition term12 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term5 (x0 : nat) := forall y0 : nat, ((Nat.sub x0 y0) = (NUMERAL 0)) = (Peano.le x0 y0).
Definition term1 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term15 := forall y0 : nat, forall y1 : nat, (Nat.sub y0 (Nat.add y0 y1)) = (NUMERAL 0).
Definition term8 (x0 : nat) := fun y0 : nat => (Nat.sub x0 (Nat.add x0 y0)) = (NUMERAL 0).
Definition term11 := forall y0 : nat, True.
Definition term9 := fun y0 : nat => True.
Definition term7 (x0 : nat) (x1 : nat) := Nat.sub x0 (Nat.add x0 x1).
Definition term3 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term10 (x0 : nat) := forall y0 : nat, (Nat.sub x0 (Nat.add x0 y0)) = (NUMERAL 0).
Definition term13 (x0 : Prop) := forall y0 : nat, x0.
