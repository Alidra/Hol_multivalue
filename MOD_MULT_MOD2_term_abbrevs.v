Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.mul y0 (Nat.modulo y2 y1)) y1) = (Nat.modulo (Nat.mul y0 y2) y1)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.mul (Nat.modulo y0 y1) y2) y1) = (Nat.modulo (Nat.mul y0 y2) y1)) x0.
Definition term20 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul x0 x1) x2.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.mul (Nat.modulo x0 x2) (Nat.modulo x1 x2)) x2).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.modulo (Nat.mul x0 (Nat.modulo y0 x1)) x1) = (Nat.modulo (Nat.mul x0 y0) x1)) x2.
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.modulo (Nat.mul (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.mul x0 y0) x1)) x2.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul x0 (Nat.modulo x1 x2)) x2.
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.mul x0 (Nat.modulo y1 y0)) y0) = (Nat.modulo (Nat.mul x0 y1) y0)) x1.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.mul (Nat.modulo x0 y0) y1) y0) = (Nat.modulo (Nat.mul x0 y1) y0)) x1.
Definition term16 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.modulo (Nat.mul (Nat.modulo x0 x1) (Nat.modulo y0 x1)) x1) = (Nat.modulo (Nat.mul x0 y0) x1).
Definition term22 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.mul (Nat.modulo x0 y0) (Nat.modulo y1 y0)) y0) = (Nat.modulo (Nat.mul x0 y1) y0).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul (Nat.modulo x0 x2) x1) x2.
Definition term25 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.mul (Nat.modulo y0 y1) (Nat.modulo y2 y1)) y1) = (Nat.modulo (Nat.mul y0 y2) y1).
Definition term23 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.mul (Nat.modulo x0 y0) (Nat.modulo y1 y0)) y0) = (Nat.modulo (Nat.mul x0 y1) y0).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.mul x0 (Nat.modulo y1 y0)) y0) = (Nat.modulo (Nat.mul x0 y1) y0).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.mul (Nat.modulo x0 y0) y1) y0) = (Nat.modulo (Nat.mul x0 y1) y0).
Definition term19 := forall y0 : nat, True.
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul (Nat.modulo x0 x2) (Nat.modulo x1 x2)) x2.
Definition term17 := fun y0 : nat => True.
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.mul x0 x1) x2).
Definition term21 (x0 : Prop) := forall y0 : nat, x0.
Definition term18 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo (Nat.mul (Nat.modulo x0 x1) (Nat.modulo y0 x1)) x1) = (Nat.modulo (Nat.mul x0 y0) x1).
Definition term10 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo (Nat.mul x0 (Nat.modulo y0 x1)) x1) = (Nat.modulo (Nat.mul x0 y0) x1).
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo (Nat.mul (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.mul x0 y0) x1).
Definition term24 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.mul (Nat.modulo y0 y1) (Nat.modulo y2 y1)) y1) = (Nat.modulo (Nat.mul y0 y2) y1).
