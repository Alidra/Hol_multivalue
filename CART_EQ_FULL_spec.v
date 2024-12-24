Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7629993 : forall {A N : Type'}, forall x : cart A N, forall y : cart A N, (x = y) = (forall i : nat, (@dollar A N x i) = (@dollar A N y i)).
