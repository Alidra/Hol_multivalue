Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3360753 : forall {A : Type'}, forall u : (A -> Prop) -> Prop, forall s : A -> Prop, ((~ (u = (@EMPTY (A -> Prop)))) /\ (forall t : A -> Prop, (@IN (A -> Prop) t u) -> @SUBSET A t s)) -> @SUBSET A (@INTERS A u) s.
