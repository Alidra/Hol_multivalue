Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3328503 : forall {_86925 : Type'}, forall P : _86925 -> Prop, forall s : (_86925 -> Prop) -> Prop, (exists x : _86925, (@IN _86925 x (@UNIONS _86925 s)) /\ (P x)) = (exists t : _86925 -> Prop, exists x : _86925, (@IN (_86925 -> Prop) t s) /\ ((@IN _86925 x t) /\ (P x))).
