Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7664494 : forall {A M N : Type'}, forall x : cart A M, forall y : cart A N, forall w : cart A M, forall z : cart A N, ((@pastecart A M N x y) = (@pastecart A M N w z)) = ((x = w) /\ (y = z)).
