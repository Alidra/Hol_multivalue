Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3278431 : forall {A : Type'}, forall x : A, (@INSERT A x (@UNIV A)) = (@UNIV A).
