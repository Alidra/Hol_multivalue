Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1203967 : forall {A : Type'}, forall l : list A, (~ (l = (@nil A))) -> (@LAST A (@List.rev A l)) = (@hd A l).
