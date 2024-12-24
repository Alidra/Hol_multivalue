Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term1 := BIT1 (NUMERAL 0).
Definition term3 := @eq nat (BIT1 0).
Definition term2 := @eq nat (BIT1 (NUMERAL 0)).
Definition term4 := NUMERAL (BIT1 0).
