Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 (S x1))) = (@IN nat y0 (dotdot x0 x1)).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term1 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (@IN nat y0 x0) = (@IN nat y0 x1).
Definition term2 (x0 : nat) (x1 : nat) := dotdot x0 (S x1).
