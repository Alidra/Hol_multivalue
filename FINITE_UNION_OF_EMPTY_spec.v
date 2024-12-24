Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4876660 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, @UNION_OF A (@FINITE (A -> Prop)) P (@EMPTY A).
