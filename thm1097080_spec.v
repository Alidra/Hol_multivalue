Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1097080 : forall {A : Type'}, ((@List.length A (@nil A)) = (NUMERAL 0)) /\ (forall h : A, forall t : list A, (@List.length A (@cons A h t)) = (S (@List.length A t))).
