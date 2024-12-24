Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4334203 : forall {A : Type'}, (@INFINITE (prod A A) (@UNIV (prod A A))) = (@INFINITE A (@UNIV A)).
