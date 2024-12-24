Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Odd (S x0).
Definition term5 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Odd y0))) x0.
Definition term1 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term12 := forall y0 : nat, Coq.Arith.PeanoNat.Nat.Odd (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term16 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term2 (x0 : nat) := (fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) x0.
Definition term8 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Odd (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term10 := fun y0 : nat => Coq.Arith.PeanoNat.Nat.Odd (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term4 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Odd y0)).
Definition term9 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term15 := forall y0 : nat, True.
Definition term11 := fun y0 : nat => ~ (Coq.Arith.PeanoNat.Nat.Odd (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term14 := fun y0 : nat => True.
Definition term0 (x0 : nat) := (fun y0 : nat => Coq.Arith.PeanoNat.Nat.Even (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x0.
Definition term7 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Odd (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term17 (x0 : Prop) := forall y0 : nat, x0.
Definition term13 := forall y0 : nat, ~ (Coq.Arith.PeanoNat.Nat.Odd (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)).
Definition term3 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Odd x0).
