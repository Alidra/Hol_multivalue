Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := (fun y0 : nat => (Nat.add (BIT1 y0) 0) = (BIT1 y0)) x0.
Definition term0 := forall y0 : nat, (Nat.add (BIT1 y0) 0) = (BIT1 y0).