Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') := (@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a0 (@UNIV a0)).
Definition term0 (a0 : Type') (a1 : Type') := (@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1)).
Definition term2 (a0 : Type') := @eq Prop (@INFINITE (prod a0 a0) (@UNIV (prod a0 a0))).
Definition term3 (a0 : Type') := @eq Prop (@INFINITE a0 (@UNIV a0)).
