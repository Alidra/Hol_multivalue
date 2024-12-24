Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4386843 : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall x : A, (@IN A x s) -> (@RESTRICTION A B s f x) = (f x).
