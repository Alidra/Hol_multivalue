Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (x0 : nat) (x1 : list a0) := ((@EL a0 (NUMERAL 0) x1) = (@hd a0 x1)) /\ ((@EL a0 (S x0) x1) = (@EL a0 x0 (@tl a0 x1))).
Definition term0 (a0 : Type') (x0 : nat) (x1 : list a0) := @EL a0 (S x0) x1.
Definition term1 (a0 : Type') (x0 : nat) (x1 : list a0) := @EL a0 x0 (@tl a0 x1).
