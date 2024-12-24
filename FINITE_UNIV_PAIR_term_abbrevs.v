Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') := (@FINITE a0 (@UNIV a0)) /\ (@FINITE a0 (@UNIV a0)).
Definition term0 (a0 : Type') (a1 : Type') := (@FINITE a0 (@UNIV a0)) /\ (@FINITE a1 (@UNIV a1)).
Definition term3 (a0 : Type') := @eq Prop (@FINITE a0 (@UNIV a0)).
Definition term2 (a0 : Type') := @eq Prop (@FINITE (prod a0 a0) (@UNIV (prod a0 a0))).
