Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : type1402 a0) := ~ (exists y0 : nat -> a0, forall y1 : nat, x0 (y0 (S y1)) (y0 y1)).
