Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (dotdot x1 x2).
Definition term2 (x0 : nat) (x1 : nat) := @IN nat x0 (dotdot x1 (NUMERAL 0)).
Definition term8 (x0 : nat) := fun y0 : nat => ~ ((Peano.le x0 y0) /\ (Peano.le y0 (NUMERAL 0))).
Definition term10 (x0 : nat) := forall y0 : nat, ~ ((Peano.le x0 y0) /\ (Peano.le y0 (NUMERAL 0))).
Definition term7 (x0 : nat) := fun y0 : nat => (@IN nat y0 (dotdot x0 (NUMERAL 0))) = (@IN nat y0 (@EMPTY nat)).
Definition term5 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x0 x1) /\ (Peano.le x1 (NUMERAL 0))).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term4 (x0 : nat) (x1 : nat) := @eq Prop (@IN nat x0 (dotdot x1 (NUMERAL 0))).
Definition term3 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 (NUMERAL 0)).
Definition term9 (x0 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 (NUMERAL 0))) = (@IN nat y0 (@EMPTY nat)).
Definition term6 (x0 : nat) (x1 : nat) := ~ ((Peano.le x0 x1) /\ (Peano.le x1 (NUMERAL 0))).
