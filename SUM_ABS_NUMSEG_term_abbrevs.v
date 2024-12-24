Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term17 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term21 := fun y0 : nat -> real => forall y1 : nat, forall y2 : nat, real_le (real_abs (@sum nat (dotdot y1 y2) y0)) (@sum nat (dotdot y1 y2) (fun y3 : nat => real_abs (y0 y3))).
Definition term19 (x0 : nat -> real) := fun y0 : nat => forall y1 : nat, real_le (real_abs (@sum nat (dotdot y0 y1) x0)) (@sum nat (dotdot y0 y1) (fun y2 : nat => real_abs (x0 y2))).
Definition term5 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> real_le (real_abs (@sum a0 y0 x0)) (@sum a0 y0 (fun y1 : a0 => real_abs (x0 y1))).
Definition term23 := forall y0 : nat -> real, forall y1 : nat, forall y2 : nat, real_le (real_abs (@sum nat (dotdot y1 y2) y0)) (@sum nat (dotdot y1 y2) (fun y3 : nat => real_abs (y0 y3))).
Definition term13 (x0 : nat) (x1 : nat -> real) := fun y0 : nat => real_le (real_abs (@sum nat (dotdot x0 y0) x1)) (@sum nat (dotdot x0 y0) (fun y1 : nat => real_abs (x1 y1))).
Definition term1 (x0 : nat) := forall y0 : nat, @FINITE nat (dotdot x0 y0).
Definition term10 (x0 : nat -> Prop) (x1 : nat -> real) := (@FINITE nat x0) -> (real_le (real_abs (@sum nat x0 x1)) (@sum nat x0 (fun y0 : nat => real_abs (x1 y0)))) = True.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (@FINITE a0 x0) -> (real_le (real_abs (@sum a0 x0 x1)) (@sum a0 x0 (fun y0 : a0 => real_abs (x1 y0)))) = True.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => @FINITE nat (dotdot x0 y0)) x1.
Definition term24 := forall y0 : nat -> real, True.
Definition term20 (x0 : nat -> real) := forall y0 : nat, forall y1 : nat, real_le (real_abs (@sum nat (dotdot y0 y1) x0)) (@sum nat (dotdot y0 y1) (fun y2 : nat => real_abs (x0 y2))).
Definition term16 := forall y0 : nat, True.
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat -> real) := (@FINITE nat (dotdot x0 x1)) -> (real_le (real_abs (@sum nat (dotdot x0 x1) x2)) (@sum nat (dotdot x0 x1) (fun y0 : nat => real_abs (x2 y0)))) = True.
Definition term4 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> real_le (real_abs (@sum a0 y1 y0)) (@sum a0 y1 (fun y2 : a0 => real_abs (y0 y2)))) x0.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat -> real) := real_le (real_abs (@sum nat (dotdot x0 x1) x2)) (@sum nat (dotdot x0 x1) (fun y0 : nat => real_abs (x2 y0))).
Definition term14 := fun y0 : nat => True.
Definition term15 (x0 : nat) (x1 : nat -> real) := forall y0 : nat, real_le (real_abs (@sum nat (dotdot x0 y0) x1)) (@sum nat (dotdot x0 y0) (fun y1 : nat => real_abs (x1 y1))).
Definition term6 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> real_le (real_abs (@sum a0 y0 x0)) (@sum a0 y0 (fun y1 : a0 => real_abs (x0 y1)))) x1.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := (@FINITE a0 x0) -> real_le (real_abs (@sum a0 x0 x1)) (@sum a0 x0 (fun y0 : a0 => real_abs (x1 y0))).
Definition term3 (x0 : nat) (x1 : nat) := @FINITE nat (dotdot x0 x1).
Definition term22 := fun y0 : nat -> real => True.
Definition term25 (x0 : Prop) := forall y0 : nat -> real, x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, @FINITE nat (dotdot y0 y1)) x0.
Definition term18 (x0 : Prop) := forall y0 : nat, x0.
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := real_le (real_abs (@sum a0 x0 x1)) (@sum a0 x0 (fun y0 : a0 => real_abs (x1 y0))).
