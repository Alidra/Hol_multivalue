Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : nat -> real) := fun y0 : nat => x0 y0.
Definition term1 (x0 : nat -> real) (x1 : nat -> Prop) (x2 : nat -> real) := (forall y0 : nat, (@IN nat y0 x1) -> (x0 y0) = (x2 y0)) -> (@sum nat x1 x0) = (@sum nat x1 x2).
Definition term0 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := (forall y0 : a0, (@IN a0 y0 x1) -> (x0 y0) = (x2 y0)) -> (@sum a0 x1 x0) = (@sum a0 x1 x2).
Definition term2 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : nat -> real) := (forall y0 : nat, (@IN nat y0 (dotdot x1 x2)) -> ((fun y1 : nat => x0 y1) y0) = (x3 y0)) -> (@sum nat (dotdot x1 x2) (fun y0 : nat => x0 y0)) = (@sum nat (dotdot x1 x2) x3).
