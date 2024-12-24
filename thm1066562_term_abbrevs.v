Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : a0) (x1 : nat -> a0) (x2 : nat) := (fun y0 : nat => (@FCONS a0 x0 x1 (S y0)) = (x1 y0)) x2.
Definition term1 (a0 : Type') (x0 : a0) (x1 : nat -> a0) (x2 : nat) := @FCONS a0 x0 x1 (S x2).
