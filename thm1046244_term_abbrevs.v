Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := S (Nat.add 0 0).
Definition term2 := (((NUMERAL (BIT1 0)) = (NUMERAL 0)) = False) -> ~ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term3 := ~ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term1 := NUMERAL (BIT1 0).
