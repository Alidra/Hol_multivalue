Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1235505 : forall {A : Type'}, forall R : A -> A -> Prop, forall R' : A -> A -> Prop, forall l : list A, ((@List.ForallOrdPairs A R l) /\ (forall x : A, forall y : A, ((@List.In A x l) /\ ((@List.In A y l) /\ (R x y))) -> R' x y)) -> @List.ForallOrdPairs A R' l.
