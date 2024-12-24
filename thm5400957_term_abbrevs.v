Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (dotdot x1 x2).
Definition term2 (x0 : nat) (x1 : nat) := @IN nat x0 (dotdot x1 (NUMERAL 0)).
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := (x1 = x0) \/ (@IN nat x1 x2).
Definition term12 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat -> Prop) := @IN nat x0 (@INSERT nat x1 x2).
Definition term5 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x0 x1) /\ (Peano.le x1 (NUMERAL 0))).
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term4 (x0 : nat) (x1 : nat) := @eq Prop (@IN nat x0 (dotdot x1 (NUMERAL 0))).
Definition term13 (x0 : nat) := (x0 = (NUMERAL 0)) \/ False.
Definition term17 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 (NUMERAL 0))) = (y0 = (NUMERAL 0)).
Definition term11 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (@IN nat x0 (@EMPTY nat)).
Definition term3 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 (NUMERAL 0)).
Definition term14 (x0 : nat) := fun y0 : nat => (@IN nat y0 (dotdot x0 (NUMERAL 0))) = (@IN nat y0 (@INSERT nat (NUMERAL 0) (@EMPTY nat))).
Definition term16 (x0 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 (NUMERAL 0))) = (@IN nat y0 (@INSERT nat (NUMERAL 0) (@EMPTY nat))).
Definition term15 (x0 : nat) := fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 (NUMERAL 0))) = (y0 = (NUMERAL 0)).
Definition term10 (x0 : nat) := @IN nat x0 (@INSERT nat (NUMERAL 0) (@EMPTY nat)).
