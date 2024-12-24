Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') := @IMAGE nat (finite_diff a0 a1) (@mk_finite_diff a0 a1) (dotdot (NUMERAL (BIT1 0)) (@COND nat (Peano.lt (@dimindex a1 (@UNIV a1)) (@dimindex a0 (@UNIV a0))) (Nat.sub (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))) (NUMERAL (BIT1 0)))).
