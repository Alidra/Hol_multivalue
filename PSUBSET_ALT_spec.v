Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3231915 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@PSUBSET A s t) = ((@SUBSET A s t) /\ (exists a : A, (@IN A a t) /\ (~ (@IN A a s)))).
