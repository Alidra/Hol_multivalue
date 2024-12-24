Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (a0 : Type') := (@HAS_SIZE (tybit1 a0) (@UNIV (tybit1 a0)) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))) (NUMERAL (BIT1 0)))) -> (@dimindex (tybit1 a0) (@UNIV (tybit1 a0))) = (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))) (NUMERAL (BIT1 0))).
Definition term1 (a0 : Type') := @HAS_SIZE (tybit0 a0) (@UNIV (tybit0 a0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))).
Definition term10 (a0 : Type') := ((@dimindex unit (@UNIV unit)) = (NUMERAL (BIT1 0))) /\ (((@dimindex (tybit0 a0) (@UNIV (tybit0 a0))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0)))) /\ ((@dimindex (tybit1 a0) (@UNIV (tybit1 a0))) = (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))) (NUMERAL (BIT1 0))))).
Definition term8 := and ((@dimindex unit (@UNIV unit)) = (NUMERAL (BIT1 0))).
Definition term4 (a0 : Type') (x0 : nat) := ((@HAS_SIZE a0 (@UNIV a0) x0) -> (@dimindex a0 (@UNIV a0)) = x0) -> (@HAS_SIZE a0 (@UNIV a0) x0) -> (@dimindex a0 (@UNIV a0)) = x0.
Definition term0 (a0 : Type') := @HAS_SIZE (tybit1 a0) (@UNIV (tybit1 a0)) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))) (NUMERAL (BIT1 0))).
Definition term14 (a0 : Type') := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0)).
Definition term13 (a0 : Type') := (@HAS_SIZE (tybit0 a0) (@UNIV (tybit0 a0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0)))) -> (@dimindex (tybit0 a0) (@UNIV (tybit0 a0))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))).
Definition term11 (a0 : Type') := True /\ (((@dimindex (tybit0 a0) (@UNIV (tybit0 a0))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0)))) /\ ((@dimindex (tybit1 a0) (@UNIV (tybit1 a0))) = (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))) (NUMERAL (BIT1 0))))).
Definition term3 (a0 : Type') (x0 : nat) := ((@HAS_SIZE a0 (@UNIV a0) x0) -> (@dimindex a0 (@UNIV a0)) = x0) -> (@dimindex a0 (@UNIV a0)) = x0.
Definition term17 (a0 : Type') := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))) (NUMERAL (BIT1 0)).
Definition term7 := @eq nat (NUMERAL (BIT1 0)).
Definition term9 (a0 : Type') := ((@dimindex (tybit0 a0) (@UNIV (tybit0 a0))) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0)))) /\ ((@dimindex (tybit1 a0) (@UNIV (tybit1 a0))) = (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))) (NUMERAL (BIT1 0)))).
Definition term15 (a0 : Type') (x0 : nat) := (@HAS_SIZE (tybit1 a0) (@UNIV (tybit1 a0)) x0) -> (@dimindex (tybit1 a0) (@UNIV (tybit1 a0))) = x0.
Definition term12 (a0 : Type') (x0 : nat) := (@HAS_SIZE (tybit0 a0) (@UNIV (tybit0 a0)) x0) -> (@dimindex (tybit0 a0) (@UNIV (tybit0 a0))) = x0.
Definition term2 (a0 : Type') (x0 : nat) := (@HAS_SIZE a0 (@UNIV a0) x0) -> (@dimindex a0 (@UNIV a0)) = x0.
Definition term6 := @eq nat (@dimindex unit (@UNIV unit)).
Definition term5 := NUMERAL (BIT1 0).
