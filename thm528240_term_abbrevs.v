Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : nat, (Nat.add 0 (BIT1 y0)) = (BIT1 y0).
Definition term1 (x0 : nat) := (fun y0 : nat => (Nat.add 0 (BIT1 y0)) = (BIT1 y0)) x0.
