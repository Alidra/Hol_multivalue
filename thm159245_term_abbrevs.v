Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term3 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term7 (x0 : nat) := Nat.modulo x0 (NUMERAL 0).
Definition term4 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term6 (x0 : nat) := (fun y0 : nat => (Nat.modulo y0 (NUMERAL 0)) = y0) x0.
Definition term14 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1).
Definition term17 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term12 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term8 (x0 : nat) := (fun y0 : nat => (Nat.div y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term2 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term0 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term1 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term10 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1).
Definition term15 := Nat.add (NUMERAL 0).
Definition term11 := Nat.mul (NUMERAL 0).
Definition term13 := Nat.mul (NUMERAL 0) (NUMERAL 0).
Definition term5 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term9 (x0 : nat) := Nat.div x0 (NUMERAL 0).
