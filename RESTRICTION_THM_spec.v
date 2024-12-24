Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4386714 : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, (@RESTRICTION A B s f) = (fun x : A => @COND B (@IN A x s) (f x) (@ARB B)).
