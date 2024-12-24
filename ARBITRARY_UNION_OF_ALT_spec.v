Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4858243 : forall {A : Type'}, forall B : (A -> Prop) -> Prop, forall s : A -> Prop, (@UNION_OF A (@ARBITRARY A) B s) = (forall x : A, (@IN A x s) -> exists u : A -> Prop, (@IN (A -> Prop) u B) /\ ((@IN A x u) /\ (@SUBSET A u s))).
