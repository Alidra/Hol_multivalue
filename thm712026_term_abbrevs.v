Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := BIT0 (S x0).
Definition term0 (x0 : nat) := S (BIT1 x0).
Definition term3 := BIT0 (S 0).
Definition term4 := BIT0 (BIT1 0).
Definition term2 := S (BIT1 0).
