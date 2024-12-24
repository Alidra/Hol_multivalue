Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term1 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (@IN nat y0 x0) = (@IN nat y0 x1).
Definition term3 := @INSERT nat (NUMERAL 0) (@EMPTY nat).
Definition term4 (x0 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 (NUMERAL 0))) = (@IN nat y0 (@INSERT nat (NUMERAL 0) (@EMPTY nat))).
Definition term2 (x0 : nat) := dotdot x0 (NUMERAL 0).
