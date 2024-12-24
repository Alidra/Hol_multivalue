Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4793256 : forall {A : Type'}, forall a : A, (@list_of_set A (@INSERT A a (@EMPTY A))) = (@cons A a (@nil A)).
