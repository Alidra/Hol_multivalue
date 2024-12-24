Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 := S (BIT0 (BIT1 0)).
Definition term2 := BIT1 (BIT1 0).
Definition term0 (x0 : nat) := S (BIT0 x0).
