Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
