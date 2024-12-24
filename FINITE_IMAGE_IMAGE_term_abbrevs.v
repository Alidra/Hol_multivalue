Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := @IMAGE nat (finite_image a0) (@finite_index a0) (dotdot (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))).
