Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1095962 : forall {A : Type'}, (forall l : list A, (@List.app A (@nil A) l) = l) /\ (forall h : A, forall t : list A, forall l : list A, (@List.app A (@cons A h t) l) = (@cons A h (@List.app A t l))).
