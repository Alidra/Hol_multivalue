Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4605902 : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@FINITE A (@UNIONS A s)) = ((@FINITE (A -> Prop) s) /\ (forall t : A -> Prop, (@IN (A -> Prop) t s) -> @FINITE A t)).
