Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : list a0, (@EL a0 (S y0) y1) = (@EL a0 y0 (@tl a0 y1))) x0.
Definition term1 (a0 : Type') (x0 : nat) := forall y0 : list a0, (@EL a0 (S x0) y0) = (@EL a0 x0 (@tl a0 y0)).
Definition term2 (a0 : Type') (x0 : nat) (x1 : list a0) := (fun y0 : list a0 => (@EL a0 (S x0) y0) = (@EL a0 x0 (@tl a0 y0))) x1.
