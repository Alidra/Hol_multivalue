Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : nat) := (@HAS_SIZE a0 (@UNIV a0) x0) -> (@dimindex a0 (@UNIV a0)) = x0.