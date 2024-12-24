Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3207453 : forall {_83983 : Type'}, forall P : _83983 -> Prop, forall a : _83983, forall s : _83983 -> Prop, (forall x : _83983, (@IN _83983 x (@INSERT _83983 a s)) -> P x) = ((P a) /\ (forall x : _83983, (@IN _83983 x s) -> P x)).
