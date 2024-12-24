Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4876895 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (P s) -> @INTERSECTION_OF A (@FINITE (A -> Prop)) P s.
