Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') := (@HAS_SIZE (tybit1 a0) (@UNIV (tybit1 a0)) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))) (NUMERAL (BIT1 0)))) -> (@dimindex (tybit1 a0) (@UNIV (tybit1 a0))) = (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))) (NUMERAL (BIT1 0))).
Definition term2 (a0 : Type') (x0 : nat) := ((@HAS_SIZE a0 (@UNIV a0) x0) -> (@dimindex a0 (@UNIV a0)) = x0) -> (@HAS_SIZE a0 (@UNIV a0) x0) -> (@dimindex a0 (@UNIV a0)) = x0.
Definition term6 (a0 : Type') := @HAS_SIZE (tybit1 a0) (@UNIV (tybit1 a0)) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))) (NUMERAL (BIT1 0))).
Definition term1 (a0 : Type') (x0 : nat) := ((@HAS_SIZE a0 (@UNIV a0) x0) -> (@dimindex a0 (@UNIV a0)) = x0) -> (@dimindex a0 (@UNIV a0)) = x0.
Definition term5 (a0 : Type') := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))) (NUMERAL (BIT1 0)).
Definition term3 (a0 : Type') (x0 : nat) := (@HAS_SIZE (tybit1 a0) (@UNIV (tybit1 a0)) x0) -> (@dimindex (tybit1 a0) (@UNIV (tybit1 a0))) = x0.
Definition term0 (a0 : Type') (x0 : nat) := (@HAS_SIZE a0 (@UNIV a0) x0) -> (@dimindex a0 (@UNIV a0)) = x0.
