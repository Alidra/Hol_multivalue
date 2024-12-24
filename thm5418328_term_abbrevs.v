Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : nat, (dotdot y0 (NUMERAL 0)) = (@COND (nat -> Prop) (y0 = (NUMERAL 0)) (@INSERT nat (NUMERAL 0) (@EMPTY nat)) (@EMPTY nat)).
