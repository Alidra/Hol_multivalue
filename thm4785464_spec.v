Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4785464 : forall {A : Type'}, ((@set_of_list A (@nil A)) = (@EMPTY A)) /\ (forall h : A, forall t : list A, (@set_of_list A (@cons A h t)) = (@INSERT A h (@set_of_list A t))).
