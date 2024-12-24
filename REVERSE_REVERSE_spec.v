Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1112270 : forall {A : Type'}, forall l : list A, (@List.rev A (@List.rev A l)) = l.
