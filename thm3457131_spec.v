Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3457131 : forall {_89578 _89597 _89598 : Type'} (P : _89598 -> _89597 -> Prop) (f : _89598 -> _89597 -> _89578 -> Prop), forall x : _89578, (exists t : _89578 -> Prop, (exists x' : _89598, exists y : _89597, (P x' y) /\ (t = (f x' y))) /\ (@IN _89578 x t)) = (exists x' : _89598, exists y : _89597, (P x' y) /\ (@IN _89578 x (f x' y))).
