Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (a0 : Type') (a1 : Type') := @eq nat (@COND nat (@FINITE (finite_diff a0 a1) (@UNIV (finite_diff a0 a1))) (@CARD (finite_diff a0 a1) (@UNIV (finite_diff a0 a1))) (NUMERAL (BIT1 0))).
Definition term18 (a0 : Type') (a1 : Type') := @eq nat (@COND nat (Peano.lt (@dimindex a1 (@UNIV a1)) (@dimindex a0 (@UNIV a0))) (Nat.sub (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))) (NUMERAL (BIT1 0))).
Definition term15 (a0 : Type') (a1 : Type') := @COND nat True (@COND nat (Peano.lt (@dimindex a1 (@UNIV a1)) (@dimindex a0 (@UNIV a0))) (Nat.sub (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))) (NUMERAL (BIT1 0))).
Definition term10 (a0 : Type') (a1 : Type') := @COND nat (@FINITE (finite_diff a0 a1) (@UNIV (finite_diff a0 a1))) (@CARD (finite_diff a0 a1) (@UNIV (finite_diff a0 a1))) (NUMERAL (BIT1 0)).
Definition term9 (a0 : Type') := @COND nat (@FINITE a0 (@UNIV a0)) (@CARD a0 (@UNIV a0)) (NUMERAL (BIT1 0)).
Definition term13 (a0 : Type') (a1 : Type') := @COND nat (@FINITE (finite_diff a0 a1) (@UNIV (finite_diff a0 a1))).
Definition term7 (a0 : Type') (a1 : Type') := @COND nat (Peano.lt (@dimindex a1 (@UNIV a1)) (@dimindex a0 (@UNIV a0))) (Nat.sub (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))) (NUMERAL (BIT1 0)).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@dimindex a0 y0) = (@COND nat (@FINITE a0 (@UNIV a0)) (@CARD a0 (@UNIV a0)) (NUMERAL (BIT1 0)))) x0.
Definition term14 (a0 : Type') (a1 : Type') := @COND nat (@FINITE (finite_diff a0 a1) (@UNIV (finite_diff a0 a1))) (@CARD (finite_diff a0 a1) (@UNIV (finite_diff a0 a1))).
Definition term4 (a0 : Type') (a1 : Type') (x0 : type31 a0 a1) (x1 : nat) := (@FINITE (finite_diff a0 a1) x0) /\ ((@CARD (finite_diff a0 a1) x0) = x1).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term5 (a0 : Type') (a1 : Type') := @HAS_SIZE (finite_diff a0 a1) (@UNIV (finite_diff a0 a1)) (@COND nat (Peano.lt (@dimindex a1 (@UNIV a1)) (@dimindex a0 (@UNIV a0))) (Nat.sub (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))) (NUMERAL (BIT1 0))).
Definition term17 (a0 : Type') (a1 : Type') := @COND nat True (@COND nat (Peano.lt (@dimindex a1 (@UNIV a1)) (@dimindex a0 (@UNIV a0))) (Nat.sub (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))) (NUMERAL (BIT1 0))) (NUMERAL (BIT1 0)).
Definition term6 (a0 : Type') (a1 : Type') := (@FINITE (finite_diff a0 a1) (@UNIV (finite_diff a0 a1))) /\ ((@CARD (finite_diff a0 a1) (@UNIV (finite_diff a0 a1))) = (@COND nat (Peano.lt (@dimindex a1 (@UNIV a1)) (@dimindex a0 (@UNIV a0))) (Nat.sub (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))) (NUMERAL (BIT1 0)))).
Definition term11 (a0 : Type') (a1 : Type') := @eq nat (@dimindex (finite_diff a0 a1) (@UNIV (finite_diff a0 a1))).
Definition term16 := NUMERAL (BIT1 0).