Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 := BIT0 (BIT1 (BIT1 0)).
Definition term0 := S (Nat.add (BIT1 (BIT0 (BIT1 0))) 0).