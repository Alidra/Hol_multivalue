Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7643282 : forall {A M N : Type'}, forall x : cart A M, forall y : cart A N, (@fstcart A M N (@pastecart A M N x y)) = x.
