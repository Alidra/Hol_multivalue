Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4839941 : forall {A : Type'}, forall u : (A -> Prop) -> Prop, forall v : (A -> Prop) -> Prop, ((@pairwise (A -> Prop) (@DISJOINT A) v) /\ (@PSUBSET (A -> Prop) u (@DELETE (A -> Prop) v (@EMPTY A)))) -> @PSUBSET A (@UNIONS A u) (@UNIONS A v).
