Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : nat) := fun y0 : nat => ((Nat.sub x0 y0) = (NUMERAL 0)) = (Peano.le x0 y0).
Definition term5 (x0 : nat) := forall y0 : nat, ((Nat.sub x0 y0) = (NUMERAL 0)) = (Peano.le x0 y0).
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.sub x0 y0) = 0) = (Peano.le x0 y0)) x1.
Definition term8 := fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = 0) = (Peano.le y0 y1).
Definition term7 := fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1).
Definition term1 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.sub x0 x1) = (NUMERAL 0)).
Definition term4 (x0 : nat) := fun y0 : nat => ((Nat.sub x0 y0) = 0) = (Peano.le x0 y0).
Definition term6 (x0 : nat) := forall y0 : nat, ((Nat.sub x0 y0) = 0) = (Peano.le x0 y0).
Definition term10 := forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = 0) = (Peano.le y0 y1).
Definition term9 := forall y0 : nat, forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1).
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = 0) = (Peano.le y0 y1)) x0.
Definition term0 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub x0 x1).
Definition term2 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.sub x0 x1) = 0).
