Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : nat) (x1 : a0) := @repeat_with_perm_args a0 (S x0) x1.
Definition term2 (a0 : Type') (x0 : nat) (x1 : a0) := ((@repeat_with_perm_args a0 (NUMERAL 0) x1) = (@nil a0)) /\ ((@repeat_with_perm_args a0 (S x0) x1) = (@cons a0 x1 (@repeat_with_perm_args a0 x0 x1))).
Definition term1 (a0 : Type') (x0 : nat) (x1 : a0) := @cons a0 x1 (@repeat_with_perm_args a0 x0 x1).
