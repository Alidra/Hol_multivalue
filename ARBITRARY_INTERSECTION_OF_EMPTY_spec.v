Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4858329 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, @INTERSECTION_OF A (@ARBITRARY A) P (@UNIV A).
