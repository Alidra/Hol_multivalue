Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1201817 : forall {A : Type'}, forall l : list A, forall m : list A, (@List.removelast A (@List.app A l m)) = (@COND (list A) (m = (@nil A)) (@List.removelast A l) (@List.app A l (@List.removelast A m))).
