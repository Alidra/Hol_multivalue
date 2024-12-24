Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3197565 : forall {A : Type'}, (@FINITE A (@EMPTY A)) /\ (forall x : A, forall s : A -> Prop, (@FINITE A s) -> @FINITE A (@INSERT A x s)).
