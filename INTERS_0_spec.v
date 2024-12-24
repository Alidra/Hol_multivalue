Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3354698 : forall {A : Type'}, (@INTERS A (@EMPTY (A -> Prop))) = (@UNIV A).
