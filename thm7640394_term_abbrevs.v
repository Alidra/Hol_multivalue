Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (a0 : Type') (a1 : Type') := Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0.
Definition term4 (a0 : Type') (a1 : Type') (x0 : type49 a0 a1) (x1 : nat) := (@FINITE (finite_sum a0 a1) x0) /\ ((@CARD (finite_sum a0 a1) x0) = x1).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term6 (a0 : Type') (a1 : Type') := (@FINITE (finite_sum a0 a1) (@UNIV (finite_sum a0 a1))) /\ ((@CARD (finite_sum a0 a1) (@UNIV (finite_sum a0 a1))) = (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term5 (a0 : Type') (a1 : Type') := @HAS_SIZE (finite_sum a0 a1) (@UNIV (finite_sum a0 a1)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))).