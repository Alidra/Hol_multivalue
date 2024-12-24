Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3197566 : forall {A : Type'}, forall a : A -> Prop, (@FINITE A a) = ((a = (@EMPTY A)) \/ (exists x : A, exists s : A -> Prop, (a = (@INSERT A x s)) /\ (@FINITE A s))).
