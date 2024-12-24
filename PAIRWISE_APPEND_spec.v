Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1231070 : forall {A : Type'}, forall R : A -> A -> Prop, forall l : list A, forall m : list A, (@List.ForallOrdPairs A R (@List.app A l m)) = ((@List.ForallOrdPairs A R l) /\ ((@List.ForallOrdPairs A R m) /\ (forall x : A, forall y : A, ((@List.In A x l) /\ (@List.In A y m)) -> R x y))).
