Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term4 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x0 (NUMERAL (BIT1 0))) x1.
Definition term17 (x0 : nat) (x1 : nat) := @eq nat (@CARD nat (dotdot x0 x1)).
Definition term6 (x0 : nat) := forall y0 : nat, @FINITE nat (dotdot x0 y0).
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => @FINITE nat (dotdot x0 y0)) x1.
Definition term25 := fun y0 : nat => forall y1 : nat, @HAS_SIZE nat (dotdot y0 y1) (Nat.sub (Nat.add y1 (NUMERAL (BIT1 0))) y0).
Definition term1 (x0 : nat) := forall y0 : nat, (@CARD nat (dotdot x0 y0)) = (Nat.sub (Nat.add y0 (NUMERAL (BIT1 0))) x0).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1.
Definition term26 := forall y0 : nat, forall y1 : nat, @HAS_SIZE nat (dotdot y0 y1) (Nat.sub (Nat.add y1 (NUMERAL (BIT1 0))) y0).
Definition term22 := forall y0 : nat, True.
Definition term3 (x0 : nat) (x1 : nat) := @CARD nat (dotdot x0 x1).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0.
Definition term20 := fun y0 : nat => True.
Definition term21 (x0 : nat) := forall y0 : nat, @HAS_SIZE nat (dotdot x0 y0) (Nat.sub (Nat.add y0 (NUMERAL (BIT1 0))) x0).
Definition term13 (x0 : nat -> Prop) (x1 : nat) := (@FINITE nat x0) /\ ((@CARD nat x0) = x1).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term19 (x0 : nat) := fun y0 : nat => @HAS_SIZE nat (dotdot x0 y0) (Nat.sub (Nat.add y0 (NUMERAL (BIT1 0))) x0).
Definition term8 (x0 : nat) (x1 : nat) := @FINITE nat (dotdot x0 x1).
Definition term16 (x0 : nat) (x1 : nat) := and (@FINITE nat (dotdot x0 x1)).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (@CARD nat (dotdot y0 y1)) = (Nat.sub (Nat.add y1 (NUMERAL (BIT1 0))) y0)) x0.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term18 (x0 : nat) (x1 : nat) := @eq nat (Nat.sub (Nat.add x0 (NUMERAL (BIT1 0))) x1).
Definition term5 (x0 : nat) := (fun y0 : nat => forall y1 : nat, @FINITE nat (dotdot y0 y1)) x0.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (@CARD nat (dotdot x0 y0)) = (Nat.sub (Nat.add y0 (NUMERAL (BIT1 0))) x0)) x1.
Definition term24 (x0 : Prop) := forall y0 : nat, x0.
Definition term15 (x0 : nat) (x1 : nat) := (@FINITE nat (dotdot x1 x0)) /\ ((@CARD nat (dotdot x1 x0)) = (Nat.sub (Nat.add x0 (NUMERAL (BIT1 0))) x1)).
Definition term14 (x0 : nat) (x1 : nat) := @HAS_SIZE nat (dotdot x1 x0) (Nat.sub (Nat.add x0 (NUMERAL (BIT1 0))) x1).
