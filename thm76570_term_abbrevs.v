Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 := forall y0 : nat, (BIT1 y0) = (S (BIT0 y0)).
Definition term0 := fun y0 : nat => S (BIT0 y0).
Definition term1 (x0 : nat) := (fun y0 : nat => S (BIT0 y0)) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => (BIT1 y0) = (S (BIT0 y0))) x0.
Definition term2 (x0 : nat) := S (BIT0 x0).
