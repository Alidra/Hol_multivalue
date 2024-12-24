Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 0) = (S (Nat.add 0 0))) x0.
Definition term9 := fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term15 (x0 : nat) := (forall y0 : nat, (Nat.pow y0 0) = (S (Nat.add 0 0))) -> (Nat.pow x0 0) = (S (Nat.add 0 0)).
Definition term6 (x0 : nat) := @eq nat (Nat.pow x0 0).
Definition term4 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term1 (x0 : nat) := S (Nat.add x0 x0).
Definition term13 := imp (forall y0 : nat, (Nat.pow y0 0) = (S (Nat.add 0 0))).
Definition term12 := imp (forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))).
Definition term2 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term8 := S (Nat.add 0 0).
Definition term0 (x0 : nat) := (fun y0 : nat => (BIT1 y0) = (S (Nat.add y0 y0))) x0.
Definition term11 := forall y0 : nat, (Nat.pow y0 0) = (S (Nat.add 0 0)).
Definition term3 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term10 := fun y0 : nat => (Nat.pow y0 0) = (S (Nat.add 0 0)).
Definition term14 (x0 : nat) := (forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) -> (Nat.pow x0 0) = (BIT1 0).
Definition term5 (x0 : nat) := @eq nat (Nat.pow x0 (NUMERAL 0)).
Definition term7 := NUMERAL (BIT1 0).
