Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) := BIT0 (S x0).
Definition term0 (x0 : nat) := (fun y0 : nat => (S (BIT1 y0)) = (BIT0 (S y0))) x0.
Definition term1 (x0 : nat) := S (BIT1 x0).
