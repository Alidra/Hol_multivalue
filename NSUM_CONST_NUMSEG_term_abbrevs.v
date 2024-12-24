Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 y1 (fun y2 : a0 => y0)) = (Nat.mul (@CARD a0 y1) y0)) x0.
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.sub (Nat.add x0 (NUMERAL (BIT1 0))) x1) x2.
Definition term28 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (@nsum nat (dotdot x0 x1) (fun y0 : nat => x2)).
Definition term4 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x0 (NUMERAL (BIT1 0))) x1.
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) := @nsum nat (dotdot x0 x1) (fun y0 : nat => x2).
Definition term6 (x0 : nat) := forall y0 : nat, @FINITE nat (dotdot x0 y0).
Definition term10 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.mul (Nat.sub (Nat.add x0 (NUMERAL (BIT1 0))) x1) x2).
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => @FINITE nat (dotdot x0 y0)) x1.
Definition term30 (x0 : nat) := fun y0 : nat => forall y1 : nat, (@nsum nat (dotdot y0 y1) (fun y2 : nat => x0)) = (Nat.mul (Nat.sub (Nat.add y1 (NUMERAL (BIT1 0))) y0) x0).
Definition term1 (x0 : nat) := forall y0 : nat, (@CARD nat (dotdot x0 y0)) = (Nat.sub (Nat.add y0 (NUMERAL (BIT1 0))) x0).
Definition term11 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) x1.
Definition term33 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (@nsum nat (dotdot y1 y2) (fun y3 : nat => y0)) = (Nat.mul (Nat.sub (Nat.add y2 (NUMERAL (BIT1 0))) y1) y0).
Definition term31 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@nsum nat (dotdot y0 y1) (fun y2 : nat => x0)) = (Nat.mul (Nat.sub (Nat.add y1 (NUMERAL (BIT1 0))) y0) x0).
Definition term27 := forall y0 : nat, True.
Definition term3 (x0 : nat) (x1 : nat) := @CARD nat (dotdot x0 x1).
Definition term25 := fun y0 : nat => True.
Definition term15 (x0 : nat -> Prop) (x1 : nat) := (@FINITE nat x0) -> (@nsum nat x0 (fun y0 : nat => x1)) = (Nat.mul (@CARD nat x0) x1).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) -> (@nsum a0 x0 (fun y0 : a0 => x1)) = (Nat.mul (@CARD a0 x0) x1).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Nat.mul (@CARD a0 x0) x1.
Definition term8 (x0 : nat) (x1 : nat) := @FINITE nat (dotdot x0 x1).
Definition term20 (x0 : nat) (x1 : nat) := Nat.mul (Nat.sub (Nat.add x0 (NUMERAL (BIT1 0))) x1).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (@CARD nat (dotdot x0 x1)) x2.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (@CARD nat (dotdot y0 y1)) = (Nat.sub (Nat.add y1 (NUMERAL (BIT1 0))) y0)) x0.
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) := (@FINITE nat (dotdot x0 x1)) -> (@nsum nat (dotdot x0 x1) (fun y0 : nat => x2)) = (Nat.mul (@CARD nat (dotdot x0 x1)) x2).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @nsum a0 x0 (fun y0 : a0 => x1).
Definition term19 (x0 : nat) (x1 : nat) := Nat.mul (@CARD nat (dotdot x0 x1)).
Definition term5 (x0 : nat) := (fun y0 : nat => forall y1 : nat, @FINITE nat (dotdot y0 y1)) x0.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (@CARD nat (dotdot x0 y0)) = (Nat.sub (Nat.add y0 (NUMERAL (BIT1 0))) x0)) x1.
Definition term29 (x0 : Prop) := forall y0 : nat, x0.
Definition term24 (x0 : nat) (x1 : nat) := fun y0 : nat => (@nsum nat (dotdot x0 y0) (fun y1 : nat => x1)) = (Nat.mul (Nat.sub (Nat.add y0 (NUMERAL (BIT1 0))) x0) x1).
Definition term32 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (@nsum nat (dotdot y1 y2) (fun y3 : nat => y0)) = (Nat.mul (Nat.sub (Nat.add y2 (NUMERAL (BIT1 0))) y1) y0).
Definition term26 (x0 : nat) (x1 : nat) := forall y0 : nat, (@nsum nat (dotdot x0 y0) (fun y1 : nat => x1)) = (Nat.mul (Nat.sub (Nat.add y0 (NUMERAL (BIT1 0))) x0) x1).
