Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) := (fun y0 : nat => (S (BIT0 y0)) = (BIT1 y0)) x0.
Definition term0 := (forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0))).
Definition term1 := forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0).
