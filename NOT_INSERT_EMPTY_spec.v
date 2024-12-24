Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3278799 : forall {A : Type'}, forall x : A, forall s : A -> Prop, ~ ((@INSERT A x s) = (@EMPTY A)).
