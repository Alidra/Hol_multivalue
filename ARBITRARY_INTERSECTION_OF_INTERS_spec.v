Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4868861 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall u : (A -> Prop) -> Prop, (forall s : A -> Prop, (@IN (A -> Prop) s u) -> @INTERSECTION_OF A (@ARBITRARY A) P s) -> @INTERSECTION_OF A (@ARBITRARY A) P (@INTERS A u).
