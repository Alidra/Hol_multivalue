Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4327456 : forall {A B : Type'}, (@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B)).
