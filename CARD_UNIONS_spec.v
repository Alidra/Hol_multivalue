Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7062799 : forall {A : Type'}, forall s : (A -> Prop) -> Prop, ((@FINITE (A -> Prop) s) /\ ((forall t : A -> Prop, (@IN (A -> Prop) t s) -> @FINITE A t) /\ (forall t : A -> Prop, forall u : A -> Prop, ((@IN (A -> Prop) t s) /\ ((@IN (A -> Prop) u s) /\ (~ (t = u)))) -> (@INTER A t u) = (@EMPTY A)))) -> (@CARD A (@UNIONS A s)) = (@nsum (A -> Prop) s (@CARD A)).
