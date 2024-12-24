Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 := (forall y0 : nat, (dotdot y0 (NUMERAL 0)) = (@COND (nat -> Prop) (y0 = (NUMERAL 0)) (@INSERT nat (NUMERAL 0) (@EMPTY nat)) (@EMPTY nat))) /\ (forall y0 : nat, forall y1 : nat, (dotdot y0 (S y1)) = (@COND (nat -> Prop) (Peano.le y0 (S y1)) (@INSERT nat (S y1) (dotdot y0 y1)) (dotdot y0 y1))).
Definition term0 := forall y0 : nat, (dotdot y0 (NUMERAL 0)) = (@COND (nat -> Prop) (y0 = (NUMERAL 0)) (@INSERT nat (NUMERAL 0) (@EMPTY nat)) (@EMPTY nat)).
