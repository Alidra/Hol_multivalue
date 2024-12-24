Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3310605 : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@SUBSET A s (@DELETE A t x)) = ((~ (@IN A x s)) /\ (@SUBSET A s t)).
