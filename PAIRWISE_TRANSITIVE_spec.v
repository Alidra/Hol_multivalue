Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1236911 : forall {A : Type'}, forall R : A -> A -> Prop, forall x : A, forall y : A, forall l : list A, (forall x' : A, forall y' : A, forall z : A, ((R x' y') /\ (R y' z)) -> R x' z) -> (@List.ForallOrdPairs A R (@cons A x (@cons A y l))) = ((R x y) /\ (@List.ForallOrdPairs A R (@cons A y l))).
