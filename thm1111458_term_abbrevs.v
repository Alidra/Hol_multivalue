Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := forall y0 : nat -> a0, forall y1 : nat, (@list_of_seq a0 y0 (S y1)) = (@List.app a0 (@list_of_seq a0 y0 y1) (@cons a0 (y0 y1) (@nil a0))).
