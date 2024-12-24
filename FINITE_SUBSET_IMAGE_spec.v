Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3698379 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, ((@FINITE B t) /\ (@SUBSET B t (@IMAGE A B f s))) = (exists s' : A -> Prop, (@FINITE A s') /\ ((@SUBSET A s' s) /\ (t = (@IMAGE A B f s')))).
