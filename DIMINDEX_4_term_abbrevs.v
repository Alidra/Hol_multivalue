Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 := @eq nat (NUMERAL (BIT0 (BIT0 (BIT1 0)))).
Definition term2 := NUMERAL (BIT0 (BIT0 (BIT1 0))).
Definition term1 := BIT0 (BIT0 (BIT1 0)).
Definition term0 := BIT0 (BIT1 0).
Definition term3 := @eq nat (@dimindex (tybit0 (tybit0 unit)) (@UNIV (tybit0 (tybit0 unit)))).
