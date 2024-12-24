Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3276312 : forall {A : Type'}, forall x : A, forall s : A -> Prop, (@IN A x s) = ((@INSERT A x s) = s).
