Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) := ((x0 = (NUMERAL 0)) -> (dotdot x0 (NUMERAL 0)) = (@INSERT nat (NUMERAL 0) (@EMPTY nat))) /\ ((~ (x0 = (NUMERAL 0))) -> (dotdot x0 (NUMERAL 0)) = (@EMPTY nat)).
Definition term0 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term2 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (dotdot x0 (NUMERAL 0)) = (@EMPTY nat).
Definition term4 (x0 : nat) := (x0 = (NUMERAL 0)) -> (dotdot x0 (NUMERAL 0)) = (@INSERT nat (NUMERAL 0) (@EMPTY nat)).
Definition term6 (x0 : nat) := @COND (nat -> Prop) (x0 = (NUMERAL 0)) (@INSERT nat (NUMERAL 0) (@EMPTY nat)) (@EMPTY nat).
Definition term3 := @INSERT nat (NUMERAL 0) (@EMPTY nat).
Definition term1 (x0 : nat) := dotdot x0 (NUMERAL 0).
