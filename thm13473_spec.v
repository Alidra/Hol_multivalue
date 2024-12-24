Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem13473 : forall {A : Type'} (_474 : A) (_475 : Prop) (_476 : A -> Prop) (_477 : A), (_476 (@COND A _475 _474 _477)) = ((_475 -> _476 _474) /\ ((~ _475) -> _476 _477)).
