Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (x0 : nat -> real) (x1 : nat -> Prop) (x2 : nat -> real) := (@FINITE nat x1) -> (@sum nat x1 (fun y0 : nat => real_sub (x0 y0) (x2 y0))) = (real_sub (@sum nat x1 x0) (@sum nat x1 x2)).
Definition term9 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := (@FINITE a0 x1) -> (@sum a0 x1 (fun y0 : a0 => real_sub (x0 y0) (x2 y0))) = (real_sub (@sum a0 x1 x0) (@sum a0 x1 x2)).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) := @eq real (@sum nat (dotdot x0 x1) (fun y0 : nat => real_sub (x2 y0) (x3 y0))).
Definition term22 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term26 (x0 : nat -> real) := fun y0 : nat -> real => forall y1 : nat, forall y2 : nat, (@sum nat (dotdot y1 y2) (fun y3 : nat => real_sub (x0 y3) (y0 y3))) = (real_sub (@sum nat (dotdot y1 y2) x0) (@sum nat (dotdot y1 y2) y0)).
Definition term13 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : nat -> real) := (@FINITE nat (dotdot x1 x2)) -> (@sum nat (dotdot x1 x2) (fun y0 : nat => real_sub (x0 y0) (x3 y0))) = (real_sub (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3)).
Definition term4 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> real, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@sum a0 y2 (fun y3 : a0 => real_sub (y0 y3) (y1 y3))) = (real_sub (@sum a0 y2 y0) (@sum a0 y2 y1))) x0.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) := @sum nat (dotdot x0 x1) (fun y0 : nat => real_sub (x2 y0) (x3 y0)).
Definition term32 := forall y0 : nat -> real, forall y1 : nat -> real, forall y2 : nat, forall y3 : nat, (@sum nat (dotdot y2 y3) (fun y4 : nat => real_sub (y0 y4) (y1 y4))) = (real_sub (@sum nat (dotdot y2 y3) y0) (@sum nat (dotdot y2 y3) y1)).
Definition term28 (x0 : nat -> real) := forall y0 : nat -> real, forall y1 : nat, forall y2 : nat, (@sum nat (dotdot y1 y2) (fun y3 : nat => real_sub (x0 y3) (y0 y3))) = (real_sub (@sum nat (dotdot y1 y2) x0) (@sum nat (dotdot y1 y2) y0)).
Definition term1 (x0 : nat) := forall y0 : nat, @FINITE nat (dotdot x0 y0).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := @sum a0 x0 (fun y0 : a0 => real_sub (x1 y0) (x2 y0)).
Definition term6 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@sum a0 y1 (fun y2 : a0 => real_sub (x0 y2) (y0 y2))) = (real_sub (@sum a0 y1 x0) (@sum a0 y1 y0))) x1.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => @FINITE nat (dotdot x0 y0)) x1.
Definition term11 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_sub (@sum a0 x1 x0) (@sum a0 x1 x2).
Definition term29 := forall y0 : nat -> real, True.
Definition term7 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@sum a0 y0 (fun y1 : a0 => real_sub (x0 y1) (x1 y1))) = (real_sub (@sum a0 y0 x0) (@sum a0 y0 x1)).
Definition term25 (x0 : nat -> real) (x1 : nat -> real) := forall y0 : nat, forall y1 : nat, (@sum nat (dotdot y0 y1) (fun y2 : nat => real_sub (x0 y2) (x1 y2))) = (real_sub (@sum nat (dotdot y0 y1) x0) (@sum nat (dotdot y0 y1) x1)).
Definition term21 := forall y0 : nat, True.
Definition term8 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@sum a0 y0 (fun y1 : a0 => real_sub (x0 y1) (x1 y1))) = (real_sub (@sum a0 y0 x0) (@sum a0 y0 x1))) x2.
Definition term15 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : nat -> real) := real_sub (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3).
Definition term19 := fun y0 : nat => True.
Definition term5 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@sum a0 y1 (fun y2 : a0 => real_sub (x0 y2) (y0 y2))) = (real_sub (@sum a0 y1 x0) (@sum a0 y1 y0)).
Definition term3 (x0 : nat) (x1 : nat) := @FINITE nat (dotdot x0 x1).
Definition term27 := fun y0 : nat -> real => True.
Definition term30 (x0 : Prop) := forall y0 : nat -> real, x0.
Definition term18 (x0 : nat -> real) (x1 : nat) (x2 : nat -> real) := fun y0 : nat => (@sum nat (dotdot x1 y0) (fun y1 : nat => real_sub (x0 y1) (x2 y1))) = (real_sub (@sum nat (dotdot x1 y0) x0) (@sum nat (dotdot x1 y0) x2)).
Definition term31 := fun y0 : nat -> real => forall y1 : nat -> real, forall y2 : nat, forall y3 : nat, (@sum nat (dotdot y2 y3) (fun y4 : nat => real_sub (y0 y4) (y1 y4))) = (real_sub (@sum nat (dotdot y2 y3) y0) (@sum nat (dotdot y2 y3) y1)).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, @FINITE nat (dotdot y0 y1)) x0.
Definition term23 (x0 : Prop) := forall y0 : nat, x0.
Definition term17 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : nat -> real) := @eq real (real_sub (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3)).
Definition term24 (x0 : nat -> real) (x1 : nat -> real) := fun y0 : nat => forall y1 : nat, (@sum nat (dotdot y0 y1) (fun y2 : nat => real_sub (x0 y2) (x1 y2))) = (real_sub (@sum nat (dotdot y0 y1) x0) (@sum nat (dotdot y0 y1) x1)).
Definition term20 (x0 : nat -> real) (x1 : nat) (x2 : nat -> real) := forall y0 : nat, (@sum nat (dotdot x1 y0) (fun y1 : nat => real_sub (x0 y1) (x2 y1))) = (real_sub (@sum nat (dotdot x1 y0) x0) (@sum nat (dotdot x1 y0) x2)).
