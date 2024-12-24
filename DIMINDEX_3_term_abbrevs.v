Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 := @eq nat (NUMERAL (BIT1 (BIT1 0))).
Definition term1 := NUMERAL (BIT1 (BIT1 0)).
Definition term0 := BIT1 (BIT1 0).
Definition term2 := @eq nat (@dimindex (tybit1 unit) (@UNIV (tybit1 unit))).
