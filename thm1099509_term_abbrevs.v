Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := forall y0 : nat, forall y1 : a0, (@repeat_with_perm_args a0 (S y0) y1) = (@cons a0 y1 (@repeat_with_perm_args a0 y0 y1)).
