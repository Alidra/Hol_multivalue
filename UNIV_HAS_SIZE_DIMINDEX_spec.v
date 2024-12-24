Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7602408 : forall {N : Type'}, (@HAS_SIZE N (@UNIV N) (@dimindex N (@UNIV N))) = (@FINITE N (@UNIV N)).
