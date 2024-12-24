Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT1 y0)) = False).
Definition term2 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True) x0.
Definition term1 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True.
