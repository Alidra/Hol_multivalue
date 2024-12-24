Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3206137 : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@IN A x (@REST A s)) = ((@IN A x s) /\ (~ (x = (@CHOICE A s)))).
