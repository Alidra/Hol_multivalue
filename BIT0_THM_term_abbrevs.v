Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) := NUMERAL (BIT0 x0).
Definition term11 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term5 (x0 : nat) := Nat.add (NUMERAL x0).
Definition term0 (x0 : nat) := (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) x0.
Definition term4 (x0 : nat) := @eq nat (Nat.add x0 x0).
Definition term1 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term9 := forall y0 : nat, (NUMERAL (BIT0 y0)) = (Nat.add (NUMERAL y0) (NUMERAL y0)).
Definition term10 := forall y0 : nat, True.
Definition term8 := fun y0 : nat => True.
Definition term7 := fun y0 : nat => (NUMERAL (BIT0 y0)) = (Nat.add (NUMERAL y0) (NUMERAL y0)).
Definition term6 (x0 : nat) := Nat.add (NUMERAL x0) (NUMERAL x0).
Definition term12 (x0 : Prop) := forall y0 : nat, x0.
Definition term3 (x0 : nat) := @eq nat (NUMERAL (BIT0 x0)).