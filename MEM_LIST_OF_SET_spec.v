Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4788386 : forall {A : Type'}, forall s : A -> Prop, (@FINITE A s) -> forall x : A, (@List.In A x (@list_of_set A s)) = (@IN A x s).
