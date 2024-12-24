Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3208694 : forall {_84024 : Type'}, forall P : _84024 -> Prop, forall a : _84024, forall s : _84024 -> Prop, (exists x : _84024, (@IN _84024 x (@INSERT _84024 a s)) /\ (P x)) = ((P a) \/ (exists x : _84024, (@IN _84024 x s) /\ (P x))).
