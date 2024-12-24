Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4333570 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@INFINITE (prod A B) (@CROSS B A s t)) = (((~ (s = (@EMPTY A))) /\ (@INFINITE B t)) \/ ((@INFINITE A s) /\ (~ (t = (@EMPTY B))))).
