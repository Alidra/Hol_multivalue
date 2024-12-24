Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3326952 : forall {_86883 : Type'}, forall P : _86883 -> Prop, forall s : (_86883 -> Prop) -> Prop, (forall x : _86883, (@IN _86883 x (@UNIONS _86883 s)) -> P x) = (forall t : _86883 -> Prop, forall x : _86883, ((@IN (_86883 -> Prop) t s) /\ (@IN _86883 x t)) -> P x).
