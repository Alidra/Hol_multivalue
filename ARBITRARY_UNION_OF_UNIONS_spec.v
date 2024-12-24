Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4868514 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall u : (A -> Prop) -> Prop, (forall s : A -> Prop, (@IN (A -> Prop) s u) -> @UNION_OF A (@ARBITRARY A) P s) -> @UNION_OF A (@ARBITRARY A) P (@UNIONS A u).
