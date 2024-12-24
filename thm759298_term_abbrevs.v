Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := BIT0 (S x0).
Definition term5 := S (BIT1 (BIT0 (BIT1 0))).
Definition term2 := S (BIT1 (BIT1 (BIT0 (BIT1 0)))).
Definition term6 := BIT0 (S (BIT0 (BIT1 0))).
Definition term0 (x0 : nat) := S (BIT1 x0).
Definition term3 := BIT0 (S (BIT1 (BIT0 (BIT1 0)))).
Definition term9 := S (BIT0 (BIT1 0)).
Definition term11 := BIT0 (BIT1 (BIT1 0)).
Definition term10 := BIT1 (BIT1 0).
Definition term7 := BIT0 (BIT1 0).
Definition term8 (x0 : nat) := S (BIT0 x0).
Definition term12 := BIT0 (BIT0 (BIT1 (BIT1 0))).
Definition term4 := BIT1 (BIT0 (BIT1 0)).
