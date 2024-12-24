Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (x0 : nat -> real) (x1 : nat) := @eq real (x0 x1).
Definition term1 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0, (@sum a0 (@INSERT a0 y1 (@EMPTY a0)) y0) = (y0 y1)) x0.
Definition term15 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term11 (x0 : nat -> real) := fun y0 : nat => (@sum nat (dotdot y0 y0) x0) = (x0 y0).
Definition term0 (x0 : nat) := (fun y0 : nat => (dotdot y0 y0) = (@INSERT nat y0 (@EMPTY nat))) x0.
Definition term8 (x0 : nat) (x1 : nat -> real) := @sum nat (@INSERT nat x0 (@EMPTY nat)) x1.
Definition term5 (x0 : nat) := @sum nat (dotdot x0 x0).
Definition term13 (x0 : nat -> real) := forall y0 : nat, (@sum nat (dotdot y0 y0) x0) = (x0 y0).
Definition term7 (x0 : nat) (x1 : nat -> real) := @sum nat (dotdot x0 x0) x1.
Definition term6 (x0 : nat) := @sum nat (@INSERT nat x0 (@EMPTY nat)).
Definition term17 := fun y0 : nat -> real => forall y1 : nat, (@sum nat (dotdot y1 y1) y0) = (y0 y1).
Definition term3 (a0 : Type') (x0 : a0 -> real) (x1 : a0) := (fun y0 : a0 => (@sum a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (x0 y0)) x1.
Definition term20 := forall y0 : nat -> real, True.
Definition term14 := forall y0 : nat, True.
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0 -> real) := @sum a0 (@INSERT a0 x0 (@EMPTY a0)) x1.
Definition term12 := fun y0 : nat => True.
Definition term19 := forall y0 : nat -> real, forall y1 : nat, (@sum nat (dotdot y1 y1) y0) = (y0 y1).
Definition term18 := fun y0 : nat -> real => True.
Definition term2 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0, (@sum a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (x0 y0).
Definition term21 (x0 : Prop) := forall y0 : nat -> real, x0.
Definition term16 (x0 : Prop) := forall y0 : nat, x0.
Definition term9 (x0 : nat) (x1 : nat -> real) := @eq real (@sum nat (dotdot x0 x0) x1).
