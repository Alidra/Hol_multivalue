Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4825471 : forall {A : Type'}, forall R : A -> A -> Prop, forall c : (A -> Prop) -> Prop, ((forall s : A -> Prop, (@IN (A -> Prop) s c) -> @pairwise A R s) /\ (forall s : A -> Prop, forall t : A -> Prop, ((@IN (A -> Prop) s c) /\ (@IN (A -> Prop) t c)) -> (@SUBSET A s t) \/ (@SUBSET A t s))) -> @pairwise A R (@UNIONS A c).
