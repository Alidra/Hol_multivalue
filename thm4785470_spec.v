Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4785470 : forall {A : Type'} (h : A) (t : list A), (fun t' : list A => (@set_of_list A (@cons A h t')) = (@INSERT A h (@set_of_list A t'))) t.
