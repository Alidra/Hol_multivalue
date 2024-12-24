Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6990845 : forall {A : Type'} (g : A -> nat), forall f : A -> nat, forall s : A -> Prop, forall t : A -> Prop, ((@FINITE A t) /\ ((@SUBSET A t s) /\ ((forall x : A, (@IN A x t) -> (f x) = (g x)) /\ (forall x : A, ((@IN A x s) /\ (~ (@IN A x t))) -> (f x) = (NUMERAL 0))))) -> (@nsum A s f) = (@nsum A t g).
