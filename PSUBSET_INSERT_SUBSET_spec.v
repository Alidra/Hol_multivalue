Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3315830 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@PSUBSET A s t) = (exists x : A, (~ (@IN A x s)) /\ (@SUBSET A (@INSERT A x s) t)).
