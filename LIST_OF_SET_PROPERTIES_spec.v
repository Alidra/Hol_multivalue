Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4786967 : forall {A : Type'}, forall s : A -> Prop, (@FINITE A s) -> ((@set_of_list A (@list_of_set A s)) = s) /\ ((@List.length A (@list_of_set A s)) = (@CARD A s)).
