Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8026123 : forall {A M N : Type'}, (@PCROSS A M N (@UNIV (cart A M)) (@UNIV (cart A N))) = (@UNIV (cart A (finite_sum M N))).
