Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1111914 : forall {A : Type'}, forall l : list A, forall m : list A, forall n : list A, (@List.app A l (@List.app A m n)) = (@List.app A (@List.app A l m) n).
