Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3560908 : forall {_91201 _91206 : Type'}, forall P : _91206 -> Prop, forall f : _91206 -> _91201, (forall x : _91206, forall y : _91206, ((P x) /\ ((P y) /\ ((f x) = (f y)))) -> x = y) = (forall x : _91206, forall y : _91206, ((P x) /\ (P y)) -> ((f x) = (f y)) = (x = y)).
