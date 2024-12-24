Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4785466 : forall {A : Type'}, (@set_of_list A (@nil A)) = (@EMPTY A).
