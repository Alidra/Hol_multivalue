Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') := (@FINITE (tybit0 a0) (@UNIV (tybit0 a0))) /\ (@FINITE (tybit1 a0) (@UNIV (tybit1 a0))).
Definition term3 (a0 : Type') := (@FINITE unit (@UNIV unit)) /\ ((@FINITE (tybit0 a0) (@UNIV (tybit0 a0))) /\ (@FINITE (tybit1 a0) (@UNIV (tybit1 a0)))).
Definition term1 (a0 : Type') := and (@FINITE (tybit0 a0) (@UNIV (tybit0 a0))).
Definition term0 := and (@FINITE unit (@UNIV unit)).
