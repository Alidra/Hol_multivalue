Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3275014 : forall {A : Type'}, forall s : A -> Prop, (s = (@EMPTY A)) \/ (exists x : A, exists t : A -> Prop, (s = (@INSERT A x t)) /\ (~ (@IN A x t))).
