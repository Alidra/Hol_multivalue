Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term27 := fun y0 : nat -> nat => True.
Definition term15 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) := Nat.add (@nsum nat (dotdot x1 x2) x0) (@nsum nat (dotdot x1 x2) x3).
Definition term17 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) := @eq nat (Nat.add (@nsum nat (dotdot x1 x2) x0) (@nsum nat (dotdot x1 x2) x3)).
Definition term22 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term26 (x0 : nat -> nat) := fun y0 : nat -> nat => forall y1 : nat, forall y2 : nat, (@nsum nat (dotdot y1 y2) (fun y3 : nat => Nat.add (x0 y3) (y0 y3))) = (Nat.add (@nsum nat (dotdot y1 y2) x0) (@nsum nat (dotdot y1 y2) y0)).
Definition term11 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Nat.add (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term4 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@nsum a0 y2 (fun y3 : a0 => Nat.add (y0 y3) (y1 y3))) = (Nat.add (@nsum a0 y2 y0) (@nsum a0 y2 y1))) x0.
Definition term32 := forall y0 : nat -> nat, forall y1 : nat -> nat, forall y2 : nat, forall y3 : nat, (@nsum nat (dotdot y2 y3) (fun y4 : nat => Nat.add (y0 y4) (y1 y4))) = (Nat.add (@nsum nat (dotdot y2 y3) y0) (@nsum nat (dotdot y2 y3) y1)).
Definition term28 (x0 : nat -> nat) := forall y0 : nat -> nat, forall y1 : nat, forall y2 : nat, (@nsum nat (dotdot y1 y2) (fun y3 : nat => Nat.add (x0 y3) (y0 y3))) = (Nat.add (@nsum nat (dotdot y1 y2) x0) (@nsum nat (dotdot y1 y2) y0)).
Definition term1 (x0 : nat) := forall y0 : nat, @FINITE nat (dotdot x0 y0).
Definition term6 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 y1 (fun y2 : a0 => Nat.add (x0 y2) (y0 y2))) = (Nat.add (@nsum a0 y1 x0) (@nsum a0 y1 y0))) x1.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => @FINITE nat (dotdot x0 y0)) x1.
Definition term13 (x0 : nat -> nat) (x1 : nat) (x2 : nat) (x3 : nat -> nat) := (@FINITE nat (dotdot x1 x2)) -> (@nsum nat (dotdot x1 x2) (fun y0 : nat => Nat.add (x0 y0) (x3 y0))) = (Nat.add (@nsum nat (dotdot x1 x2) x0) (@nsum nat (dotdot x1 x2) x3)).
Definition term18 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> nat) := fun y0 : nat => (@nsum nat (dotdot x1 y0) (fun y1 : nat => Nat.add (x0 y1) (x2 y1))) = (Nat.add (@nsum nat (dotdot x1 y0) x0) (@nsum nat (dotdot x1 y0) x2)).
Definition term29 := forall y0 : nat -> nat, True.
Definition term7 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => Nat.add (x0 y1) (x1 y1))) = (Nat.add (@nsum a0 y0 x0) (@nsum a0 y0 x1)).
Definition term25 (x0 : nat -> nat) (x1 : nat -> nat) := forall y0 : nat, forall y1 : nat, (@nsum nat (dotdot y0 y1) (fun y2 : nat => Nat.add (x0 y2) (x1 y2))) = (Nat.add (@nsum nat (dotdot y0 y1) x0) (@nsum nat (dotdot y0 y1) x1)).
Definition term21 := forall y0 : nat, True.
Definition term8 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => Nat.add (x0 y1) (x1 y1))) = (Nat.add (@nsum a0 y0 x0) (@nsum a0 y0 x1))) x2.
Definition term19 := fun y0 : nat => True.
Definition term5 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 y1 (fun y2 : a0 => Nat.add (x0 y2) (y0 y2))) = (Nat.add (@nsum a0 y1 x0) (@nsum a0 y1 y0)).
Definition term3 (x0 : nat) (x1 : nat) := @FINITE nat (dotdot x0 x1).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat -> nat) := @eq nat (@nsum nat (dotdot x0 x1) (fun y0 : nat => Nat.add (x2 y0) (x3 y0))).
Definition term30 (x0 : Prop) := forall y0 : nat -> nat, x0.
Definition term31 := fun y0 : nat -> nat => forall y1 : nat -> nat, forall y2 : nat, forall y3 : nat, (@nsum nat (dotdot y2 y3) (fun y4 : nat => Nat.add (y0 y4) (y1 y4))) = (Nat.add (@nsum nat (dotdot y2 y3) y0) (@nsum nat (dotdot y2 y3) y1)).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, @FINITE nat (dotdot y0 y1)) x0.
Definition term23 (x0 : Prop) := forall y0 : nat, x0.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat -> nat) (x3 : nat -> nat) := @nsum nat (dotdot x0 x1) (fun y0 : nat => Nat.add (x2 y0) (x3 y0)).
Definition term12 (x0 : nat -> nat) (x1 : nat -> Prop) (x2 : nat -> nat) := (@FINITE nat x1) -> (@nsum nat x1 (fun y0 : nat => Nat.add (x0 y0) (x2 y0))) = (Nat.add (@nsum nat x1 x0) (@nsum nat x1 x2)).
Definition term9 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (@FINITE a0 x1) -> (@nsum a0 x1 (fun y0 : a0 => Nat.add (x0 y0) (x2 y0))) = (Nat.add (@nsum a0 x1 x0) (@nsum a0 x1 x2)).
Definition term24 (x0 : nat -> nat) (x1 : nat -> nat) := fun y0 : nat => forall y1 : nat, (@nsum nat (dotdot y0 y1) (fun y2 : nat => Nat.add (x0 y2) (x1 y2))) = (Nat.add (@nsum nat (dotdot y0 y1) x0) (@nsum nat (dotdot y0 y1) x1)).
Definition term20 (x0 : nat -> nat) (x1 : nat) (x2 : nat -> nat) := forall y0 : nat, (@nsum nat (dotdot x1 y0) (fun y1 : nat => Nat.add (x0 y1) (x2 y1))) = (Nat.add (@nsum nat (dotdot x1 y0) x0) (@nsum nat (dotdot x1 y0) x2)).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := @nsum a0 x0 (fun y0 : a0 => Nat.add (x1 y0) (x2 y0)).
