Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : Prop) := (x0 /\ (~ x0)) -> False.
Definition term4 (x0 : Prop) := ~ (x0 /\ (~ x0)).
Definition term18 := forall y0 : nat, ~ ((Coq.Arith.PeanoNat.Nat.Even y0) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)).
Definition term1 (x0 : Prop) := (fun y0 : Prop => y0 -> False) x0.
Definition term20 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term5 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term13 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) /\ (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term9 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term8 := forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term7 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term2 (x0 : Prop) := @eq Prop (~ x0).
Definition term19 := forall y0 : nat, True.
Definition term15 (x0 : nat) := ~ ((Coq.Arith.PeanoNat.Nat.Even x0) /\ (Coq.Arith.PeanoNat.Nat.Odd x0)).
Definition term17 := fun y0 : nat => True.
Definition term14 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) /\ (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term6 := fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term12 (x0 : nat) := and (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term21 (x0 : Prop) := forall y0 : nat, x0.
Definition term10 (x0 : Prop) := (~ (x0 /\ (~ x0))) -> (x0 /\ (~ x0)) = False.
Definition term16 := fun y0 : nat => ~ ((Coq.Arith.PeanoNat.Nat.Even y0) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)).
Definition term0 (x0 : Prop) := x0 /\ (~ x0).
Definition term11 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0.
