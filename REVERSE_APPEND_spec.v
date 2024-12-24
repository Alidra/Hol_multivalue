Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1112107 : forall {A : Type'}, forall l : list A, forall m : list A, (@List.rev A (@List.app A l m)) = (@List.app A (@List.rev A m) (@List.rev A l)).
