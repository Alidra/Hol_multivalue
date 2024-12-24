Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4876701 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, @INTERSECTION_OF A (@FINITE (A -> Prop)) P (@UNIV A).
