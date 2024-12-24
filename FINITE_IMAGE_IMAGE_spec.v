Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7604550 : forall {A : Type'}, (@UNIV (finite_image A)) = (@IMAGE nat (finite_image A) (@finite_index A) (dotdot (NUMERAL (BIT1 0)) (@dimindex A (@UNIV A)))).
