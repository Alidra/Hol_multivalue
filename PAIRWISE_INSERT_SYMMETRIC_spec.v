Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4810017 : forall {A : Type'}, forall r : A -> A -> Prop, forall x : A, forall s : A -> Prop, (forall y : A, (@IN A y s) -> (r x y) = (r y x)) -> (@pairwise A r (@INSERT A x s)) = ((forall y : A, ((@IN A y s) /\ (~ (y = x))) -> r x y) /\ (@pairwise A r s)).
