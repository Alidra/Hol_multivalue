Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := (@INFINITE a0 (@UNIV a0)) \/ (@INFINITE a1 (@UNIV a1)).
