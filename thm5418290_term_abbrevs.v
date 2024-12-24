Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 (NUMERAL 0))) = (@IN nat y0 (@INSERT nat (NUMERAL 0) (@EMPTY nat))).
