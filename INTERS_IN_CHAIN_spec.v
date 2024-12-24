Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3781456 : forall {A : Type'}, forall f : (A -> Prop) -> Prop, ((@FINITE (A -> Prop) f) /\ ((~ (f = (@EMPTY (A -> Prop)))) /\ (forall s : A -> Prop, forall t : A -> Prop, ((@IN (A -> Prop) s f) /\ (@IN (A -> Prop) t f)) -> (@SUBSET A s t) \/ (@SUBSET A t s)))) -> @IN (A -> Prop) (@INTERS A f) f.
