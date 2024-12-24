Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1116758 : forall {A B : Type'}, forall f : A -> B, forall l1 : list A, forall l2 : list A, (@List.map A B f (@List.app A l1 l2)) = (@List.app B (@List.map A B f l1) (@List.map A B f l2)).
