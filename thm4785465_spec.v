Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4785465 : forall {A : Type'}, forall h : A, forall t : list A, (@set_of_list A (@cons A h t)) = (@INSERT A h (@set_of_list A t)).
