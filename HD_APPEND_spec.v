Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1206885 : forall {A : Type'}, forall l : list A, forall m : list A, (@hd A (@List.app A l m)) = (@COND A (l = (@nil A)) (@hd A m) (@hd A l)).
