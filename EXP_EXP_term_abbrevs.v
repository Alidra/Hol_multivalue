Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow y0 (Nat.mul y1 y2)) = (Nat.pow (Nat.pow y0 y1) y2)) x0.
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.pow (Nat.pow x0 x1) x2).
Definition term12 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.pow x0 (Nat.mul x1 y0)) = (Nat.pow (Nat.pow x0 x1) y0).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1)) x1.
Definition term17 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.pow y0 y1) y2) = (Nat.pow y0 (Nat.mul y1 y2)).
Definition term15 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.pow (Nat.pow x0 y0) y1) = (Nat.pow x0 (Nat.mul y0 y1)).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.pow x0 (Nat.mul y0 y1)) = (Nat.pow (Nat.pow x0 y0) y1).
Definition term11 := forall y0 : nat, True.
Definition term8 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.pow (Nat.pow x0 x1) y0) = (Nat.pow x0 (Nat.mul x1 y0)).
Definition term9 := fun y0 : nat => True.
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.pow x0 (Nat.mul x1 y0)) = (Nat.pow (Nat.pow x0 x1) y0)) x2.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow x0 (Nat.mul x1 x2).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow (Nat.pow x0 x1) x2.
Definition term13 (x0 : Prop) := forall y0 : nat, x0.
Definition term10 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.pow (Nat.pow x0 x1) y0) = (Nat.pow x0 (Nat.mul x1 y0)).
Definition term14 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.pow (Nat.pow x0 y0) y1) = (Nat.pow x0 (Nat.mul y0 y1)).
Definition term16 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.pow (Nat.pow y0 y1) y2) = (Nat.pow y0 (Nat.mul y1 y2)).
