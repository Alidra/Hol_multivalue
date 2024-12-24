Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : nat) := (((@dimindex a0 (@UNIV a0)) = x0) = ((@dimindex (tybit1 a0) (@UNIV (tybit1 a0))) = (BIT1 x0))) /\ ((@dimindex unit (@UNIV unit)) = (BIT1 0)).
