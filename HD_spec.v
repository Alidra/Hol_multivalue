Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1094867 : forall {A : Type'} (t : list A) (h : A), (@hd A (@cons A h t)) = h.
