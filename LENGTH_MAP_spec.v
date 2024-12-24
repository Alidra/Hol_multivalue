Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1116924 : forall {A B : Type'}, forall l : list A, forall f : A -> B, (@List.length B (@List.map A B f l)) = (@List.length A l).
