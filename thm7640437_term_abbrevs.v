Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (a0 : Type') (a1 : Type') := @eq nat (@COND nat (@FINITE (finite_sum a0 a1) (@UNIV (finite_sum a0 a1))) (@CARD (finite_sum a0 a1) (@UNIV (finite_sum a0 a1))) (NUMERAL (BIT1 0))).
Definition term1 (a0 : Type') (a1 : Type') := Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)).
Definition term5 (a0 : Type') (a1 : Type') := @COND nat (@FINITE (finite_sum a0 a1) (@UNIV (finite_sum a0 a1))) (@CARD (finite_sum a0 a1) (@UNIV (finite_sum a0 a1))) (NUMERAL (BIT1 0)).
Definition term0 (a0 : Type') (a1 : Type') := @COND nat (@FINITE (finite_sum a0 a1) (@UNIV (finite_sum a0 a1))).
Definition term6 (a0 : Type') (a1 : Type') := @COND nat True (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))) (NUMERAL (BIT1 0)).
Definition term8 (a0 : Type') (a1 : Type') := @eq nat (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))).
Definition term3 (a0 : Type') (a1 : Type') := @COND nat True (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))).
Definition term2 (a0 : Type') (a1 : Type') := @COND nat (@FINITE (finite_sum a0 a1) (@UNIV (finite_sum a0 a1))) (@CARD (finite_sum a0 a1) (@UNIV (finite_sum a0 a1))).
Definition term4 := NUMERAL (BIT1 0).
