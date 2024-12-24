Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7156962 : forall {A : Type'} (g : A -> real), forall f : A -> real, forall s : A -> Prop, forall t : A -> Prop, ((@FINITE A t) /\ ((@SUBSET A t s) /\ ((forall x : A, (@IN A x t) -> (f x) = (g x)) /\ (forall x : A, ((@IN A x s) /\ (~ (@IN A x t))) -> (f x) = (real_of_num (NUMERAL 0)))))) -> (@sum A s f) = (@sum A t g).
