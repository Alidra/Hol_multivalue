Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 := (@HAS_SIZE unit (@UNIV unit) (NUMERAL (BIT1 0))) -> (@dimindex unit (@UNIV unit)) = (NUMERAL (BIT1 0)).
Definition term1 (x0 : nat) := (@HAS_SIZE unit (@UNIV unit) x0) -> (@dimindex unit (@UNIV unit)) = x0.
Definition term0 (a0 : Type') (x0 : nat) := (@HAS_SIZE a0 (@UNIV a0) x0) -> (@dimindex a0 (@UNIV a0)) = x0.
Definition term3 := NUMERAL (BIT1 0).
