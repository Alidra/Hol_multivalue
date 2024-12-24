Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2427819 : forall {A : Type'}, forall rel : A -> A -> Prop, forall x : A, forall y : A, (@eq2 A x y rel) = (rel x y).
