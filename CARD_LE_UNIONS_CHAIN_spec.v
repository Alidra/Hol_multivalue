Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4108815 : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall n : nat, ((forall t : A -> Prop, forall u : A -> Prop, ((@IN (A -> Prop) t f) /\ (@IN (A -> Prop) u f)) -> (@SUBSET A t u) \/ (@SUBSET A u t)) /\ (forall t : A -> Prop, (@IN (A -> Prop) t f) -> (@FINITE A t) /\ (Peano.le (@CARD A t) n))) -> (@FINITE A (@UNIONS A f)) /\ (Peano.le (@CARD A (@UNIONS A f)) n).
