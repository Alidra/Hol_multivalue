Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := @nsum a0 x0 (fun y0 : a0 => Nat.mul (x1 y0) x2).
Definition term20 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) := forall y0 : a0 -> Prop, (@nsum a0 y0 (fun y1 : a0 => Nat.mul (x0 y1) x1)) = (Nat.mul (@nsum a0 y0 x0) x1).
Definition term6 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Nat.mul x0 (@nsum a0 x1 x2).
Definition term31 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := @eq nat (@nsum a0 x0 (fun y0 : a0 => Nat.mul (x1 y0) x2)).
Definition term36 (a0 : Type') := fun y0 : a0 -> nat => True.
Definition term27 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : nat, forall y2 : a0 -> Prop, (@nsum a0 y2 (fun y3 : a0 => Nat.mul y1 (y0 y3))) = (Nat.mul y1 (@nsum a0 y2 y0)).
Definition term26 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : nat, forall y2 : a0 -> Prop, (@nsum a0 y2 (fun y3 : a0 => Nat.mul (y0 y3) y1)) = (Nat.mul (@nsum a0 y2 y0) y1).
Definition term21 (a0 : Type') (x0 : a0 -> nat) := fun y0 : nat => forall y1 : a0 -> Prop, (@nsum a0 y1 (fun y2 : a0 => Nat.mul (x0 y2) y0)) = (Nat.mul (@nsum a0 y1 x0) y0).
Definition term0 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : nat, forall y2 : a0 -> Prop, (@nsum a0 y2 (fun y3 : a0 => Nat.mul y1 (y0 y3))) = (Nat.mul y1 (@nsum a0 y2 y0))) x0.
Definition term38 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> nat, x0.
Definition term32 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term4 (a0 : Type') (x0 : nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => Nat.mul x0 (x1 y1))) = (Nat.mul x0 (@nsum a0 y0 x1))) x2.
Definition term2 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) := (fun y0 : nat => forall y1 : a0 -> Prop, (@nsum a0 y1 (fun y2 : a0 => Nat.mul y0 (x0 y2))) = (Nat.mul y0 (@nsum a0 y1 x0))) x1.
Definition term25 (a0 : Type') := fun y0 : a0 -> nat => forall y1 : nat, forall y2 : a0 -> Prop, (@nsum a0 y2 (fun y3 : a0 => Nat.mul y1 (y0 y3))) = (Nat.mul y1 (@nsum a0 y2 y0)).
Definition term24 (a0 : Type') := fun y0 : a0 -> nat => forall y1 : nat, forall y2 : a0 -> Prop, (@nsum a0 y2 (fun y3 : a0 => Nat.mul (y0 y3) y1)) = (Nat.mul (@nsum a0 y2 y0) y1).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := Nat.mul (@nsum a0 x0 x1) x2.
Definition term18 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) := fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => Nat.mul (x0 y1) x1)) = (Nat.mul (@nsum a0 y0 x0) x1).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> nat) := @nsum a0 x0 (fun y0 : a0 => Nat.mul x1 (x2 y0)).
Definition term13 (a0 : Type') (x0 : nat) (x1 : a0 -> nat) := fun y0 : a0 => Nat.mul x0 (x1 y0).
Definition term23 (a0 : Type') (x0 : a0 -> nat) := forall y0 : nat, forall y1 : a0 -> Prop, (@nsum a0 y1 (fun y2 : a0 => Nat.mul (x0 y2) y0)) = (Nat.mul (@nsum a0 y1 x0) y0).
Definition term1 (a0 : Type') (x0 : a0 -> nat) := forall y0 : nat, forall y1 : a0 -> Prop, (@nsum a0 y1 (fun y2 : a0 => Nat.mul y0 (x0 y2))) = (Nat.mul y0 (@nsum a0 y1 x0)).
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> nat) := @eq nat (@nsum a0 x0 (fun y0 : a0 => Nat.mul x1 (x2 y0))).
Definition term19 (a0 : Type') (x0 : nat) (x1 : a0 -> nat) := fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => Nat.mul x0 (x1 y1))) = (Nat.mul x0 (@nsum a0 y0 x1)).
Definition term34 := forall y0 : nat, True.
Definition term33 := fun y0 : nat => True.
Definition term8 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term29 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term10 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : nat) := Nat.mul (x0 x1) x2.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term12 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) := fun y0 : a0 => Nat.mul (x0 y0) x1.
Definition term11 (a0 : Type') (x0 : nat) (x1 : a0 -> nat) (x2 : a0) := Nat.mul x0 (x1 x2).
Definition term22 (a0 : Type') (x0 : a0 -> nat) := fun y0 : nat => forall y1 : a0 -> Prop, (@nsum a0 y1 (fun y2 : a0 => Nat.mul y0 (x0 y2))) = (Nat.mul y0 (@nsum a0 y1 x0)).
Definition term35 (x0 : Prop) := forall y0 : nat, x0.
Definition term3 (a0 : Type') (x0 : nat) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, (@nsum a0 y0 (fun y1 : a0 => Nat.mul x0 (x1 y1))) = (Nat.mul x0 (@nsum a0 y0 x1)).
Definition term28 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := @eq nat (Nat.mul x0 (@nsum a0 x1 x2)).
Definition term37 (a0 : Type') := forall y0 : a0 -> nat, True.
Definition term30 (a0 : Type') := forall y0 : a0 -> Prop, True.
