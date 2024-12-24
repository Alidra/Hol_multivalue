Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (a0 : Type') (x0 : finite_sum a0 a0) (x1 : finite_sum a0 a0) := imp (x0 = x1).
Definition term15 (a0 : Type') := forall y0 : finite_sum a0 a0, True.
Definition term16 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term13 (a0 : Type') := fun y0 : finite_sum a0 a0 => True.
Definition term1 (a0 : Type') (x0 : type46 a0) (x1 : type48 a0) (x2 : nat) := ((forall y0 : finite_sum a0 a0, forall y1 : finite_sum a0 a0, ((@IN (finite_sum a0 a0) y0 x1) /\ ((@IN (finite_sum a0 a0) y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) /\ (@HAS_SIZE (finite_sum a0 a0) x1 x2)) -> @HAS_SIZE (tybit0 a0) (@IMAGE (finite_sum a0 a0) (tybit0 a0) x0 x1) x2.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) (x2 : nat) := ((forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x1) /\ ((@IN a0 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) /\ (@HAS_SIZE a0 x1 x2)) -> @HAS_SIZE a1 (@IMAGE a0 a1 x0 x1) x2.
Definition term12 (a0 : Type') (x0 : finite_sum a0 a0) := fun y0 : finite_sum a0 a0 => ((@IN (finite_sum a0 a0) x0 (@UNIV (finite_sum a0 a0))) /\ ((@IN (finite_sum a0 a0) y0 (@UNIV (finite_sum a0 a0))) /\ ((@mktybit0 a0 x0) = (@mktybit0 a0 y0)))) -> x0 = y0.
Definition term31 (a0 : Type') := (@HAS_SIZE (finite_sum a0 a0) (@UNIV (finite_sum a0 a0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0)))) -> @HAS_SIZE (finite_sum a0 a0) (@UNIV (finite_sum a0 a0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))).
Definition term30 (a0 : Type') := (@HAS_SIZE (finite_sum a0 a0) (@UNIV (finite_sum a0 a0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a0 (@UNIV a0)))) -> @HAS_SIZE (finite_sum a0 a0) (@UNIV (finite_sum a0 a0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))).
Definition term11 (a0 : Type') (x0 : finite_sum a0 a0) (x1 : finite_sum a0 a0) := (x0 = x1) -> x0 = x1.
Definition term4 (a0 : Type') (x0 : finite_sum a0 a0) := and (@IN (finite_sum a0 a0) x0 (@UNIV (finite_sum a0 a0))).
Definition term22 (a0 : Type') := (forall y0 : finite_sum a0 a0, forall y1 : finite_sum a0 a0, ((@IN (finite_sum a0 a0) y0 (@UNIV (finite_sum a0 a0))) /\ ((@IN (finite_sum a0 a0) y1 (@UNIV (finite_sum a0 a0))) /\ ((@mktybit0 a0 y0) = (@mktybit0 a0 y1)))) -> y0 = y1) /\ (@HAS_SIZE (finite_sum a0 a0) (@UNIV (finite_sum a0 a0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0)))).
Definition term33 (a0 : Type') := @HAS_SIZE (tybit0 a0) (@UNIV (tybit0 a0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))).
Definition term21 (a0 : Type') := @HAS_SIZE (finite_sum a0 a0) (@UNIV (finite_sum a0 a0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))).
Definition term32 (a0 : Type') := @HAS_SIZE (tybit0 a0) (@IMAGE (finite_sum a0 a0) (tybit0 a0) (@mktybit0 a0) (@UNIV (finite_sum a0 a0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))).
Definition term27 (a0 : Type') := Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a0 (@UNIV a0)).
Definition term26 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term3 (a0 : Type') := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0)).
Definition term8 (a0 : Type') (x0 : finite_sum a0 a0) (x1 : finite_sum a0 a0) := imp ((@IN (finite_sum a0 a0) x0 (@UNIV (finite_sum a0 a0))) /\ ((@IN (finite_sum a0 a0) x1 (@UNIV (finite_sum a0 a0))) /\ ((@mktybit0 a0 x0) = (@mktybit0 a0 x1)))).
Definition term19 (a0 : Type') := forall y0 : finite_sum a0 a0, forall y1 : finite_sum a0 a0, ((@IN (finite_sum a0 a0) y0 (@UNIV (finite_sum a0 a0))) /\ ((@IN (finite_sum a0 a0) y1 (@UNIV (finite_sum a0 a0))) /\ ((@mktybit0 a0 y0) = (@mktybit0 a0 y1)))) -> y0 = y1.
Definition term5 (a0 : Type') (x0 : finite_sum a0 a0) (x1 : finite_sum a0 a0) := (@IN (finite_sum a0 a0) x1 (@UNIV (finite_sum a0 a0))) /\ ((@mktybit0 a0 x0) = (@mktybit0 a0 x1)).
Definition term29 (a0 : Type') := imp (@HAS_SIZE (finite_sum a0 a0) (@UNIV (finite_sum a0 a0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0)))).
Definition term7 (a0 : Type') (x0 : finite_sum a0 a0) (x1 : finite_sum a0 a0) := (@IN (finite_sum a0 a0) x0 (@UNIV (finite_sum a0 a0))) /\ ((@IN (finite_sum a0 a0) x1 (@UNIV (finite_sum a0 a0))) /\ ((@mktybit0 a0 x0) = (@mktybit0 a0 x1))).
Definition term20 (a0 : Type') := and (forall y0 : finite_sum a0 a0, forall y1 : finite_sum a0 a0, ((@IN (finite_sum a0 a0) y0 (@UNIV (finite_sum a0 a0))) /\ ((@IN (finite_sum a0 a0) y1 (@UNIV (finite_sum a0 a0))) /\ ((@mktybit0 a0 y0) = (@mktybit0 a0 y1)))) -> y0 = y1).
Definition term10 (a0 : Type') (x0 : finite_sum a0 a0) (x1 : finite_sum a0 a0) := ((@IN (finite_sum a0 a0) x0 (@UNIV (finite_sum a0 a0))) /\ ((@IN (finite_sum a0 a0) x1 (@UNIV (finite_sum a0 a0))) /\ ((@mktybit0 a0 x0) = (@mktybit0 a0 x1)))) -> x0 = x1.
Definition term23 (a0 : Type') := True /\ (@HAS_SIZE (finite_sum a0 a0) (@UNIV (finite_sum a0 a0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0)))).
Definition term17 (a0 : Type') (x0 : Prop) := forall y0 : finite_sum a0 a0, x0.
Definition term25 (a0 : Type') := @HAS_SIZE (finite_sum a0 a0) (@UNIV (finite_sum a0 a0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a0 (@UNIV a0))).
Definition term24 (a0 : Type') (a1 : Type') := @HAS_SIZE (finite_sum a0 a1) (@UNIV (finite_sum a0 a1)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))).
Definition term28 (a0 : Type') := imp (@HAS_SIZE (finite_sum a0 a0) (@UNIV (finite_sum a0 a0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a0 (@UNIV a0)))).
Definition term14 (a0 : Type') (x0 : finite_sum a0 a0) := forall y0 : finite_sum a0 a0, ((@IN (finite_sum a0 a0) x0 (@UNIV (finite_sum a0 a0))) /\ ((@IN (finite_sum a0 a0) y0 (@UNIV (finite_sum a0 a0))) /\ ((@mktybit0 a0 x0) = (@mktybit0 a0 y0)))) -> x0 = y0.
Definition term6 (a0 : Type') (x0 : finite_sum a0 a0) (x1 : finite_sum a0 a0) := True /\ (x0 = x1).
Definition term18 (a0 : Type') := fun y0 : finite_sum a0 a0 => forall y1 : finite_sum a0 a0, ((@IN (finite_sum a0 a0) y0 (@UNIV (finite_sum a0 a0))) /\ ((@IN (finite_sum a0 a0) y1 (@UNIV (finite_sum a0 a0))) /\ ((@mktybit0 a0 y0) = (@mktybit0 a0 y1)))) -> y0 = y1.
Definition term2 (a0 : Type') := ((forall y0 : finite_sum a0 a0, forall y1 : finite_sum a0 a0, ((@IN (finite_sum a0 a0) y0 (@UNIV (finite_sum a0 a0))) /\ ((@IN (finite_sum a0 a0) y1 (@UNIV (finite_sum a0 a0))) /\ ((@mktybit0 a0 y0) = (@mktybit0 a0 y1)))) -> y0 = y1) /\ (@HAS_SIZE (finite_sum a0 a0) (@UNIV (finite_sum a0 a0)) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))))) -> @HAS_SIZE (tybit0 a0) (@IMAGE (finite_sum a0 a0) (tybit0 a0) (@mktybit0 a0) (@UNIV (finite_sum a0 a0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (@dimindex a0 (@UNIV a0))).
