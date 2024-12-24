Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3789348 : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall s : A -> Prop, ((@FINITE A s) /\ ((@SUBSET A s (@UNIONS A f)) /\ ((~ (f = (@EMPTY (A -> Prop)))) /\ (forall t : A -> Prop, forall u : A -> Prop, ((@IN (A -> Prop) t f) /\ (@IN (A -> Prop) u f)) -> (@SUBSET A t u) \/ (@SUBSET A u t))))) -> exists t : A -> Prop, (@IN (A -> Prop) t f) /\ (@SUBSET A s t).
