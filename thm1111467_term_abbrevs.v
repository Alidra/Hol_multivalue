Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @list_of_seq a0 x0 (S x1).
Definition term0 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := (fun y0 : nat => (@list_of_seq a0 x0 (S y0)) = (@List.app a0 (@list_of_seq a0 x0 y0) (@cons a0 (x0 y0) (@nil a0)))) x1.
Definition term2 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @List.app a0 (@list_of_seq a0 x0 x1) (@cons a0 (x0 x1) (@nil a0)).
