Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7661 : forall {_1718 : Type'}, forall R : _1718 -> _1718 -> Prop, forall P : _1718 -> _1718 -> Prop, ((forall x : _1718, forall y : _1718, (P x y) -> P y x) /\ ((forall x : _1718, forall y : _1718, (R x y) \/ (R y x)) /\ (forall x : _1718, forall y : _1718, (R x y) -> P x y))) -> forall x : _1718, forall y : _1718, P x y.
