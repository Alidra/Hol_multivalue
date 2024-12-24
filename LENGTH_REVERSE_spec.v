Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1118493 : forall {A : Type'}, forall l : list A, (@List.length A (@List.rev A l)) = (@List.length A l).
