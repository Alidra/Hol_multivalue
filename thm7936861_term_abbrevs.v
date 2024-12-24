Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := ((@dimindex (tybit0 a0) (@UNIV (tybit0 a0))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0)))) /\ ((@dimindex (tybit1 a0) (@UNIV (tybit1 a0))) = (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))) (NUMERAL (BIT1 0)))).
