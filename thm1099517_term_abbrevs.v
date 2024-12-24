Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (x0 : nat) := forall y0 : a0, (@repeat_with_perm_args a0 (S x0) y0) = (@cons a0 y0 (@repeat_with_perm_args a0 x0 y0)).
Definition term0 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, (@repeat_with_perm_args a0 (S y0) y1) = (@cons a0 y1 (@repeat_with_perm_args a0 y0 y1))) x0.
Definition term2 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => (@repeat_with_perm_args a0 (S x0) y0) = (@cons a0 y0 (@repeat_with_perm_args a0 x0 y0))) x1.
