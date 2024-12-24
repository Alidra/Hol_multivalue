Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3350696 : forall {A : Type'}, (@UNIONS A (@UNIV (A -> Prop))) = (@UNIV A).
