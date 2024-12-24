Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7932948 : forall {A : Type'}, (@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))).
