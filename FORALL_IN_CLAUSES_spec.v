Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5031264 : forall {_113480 _113520 : Type'}, (forall P : _113480 -> Prop, (forall x : _113480, (@IN _113480 x (@EMPTY _113480)) -> P x) = True) /\ (forall P : _113520 -> Prop, forall a : _113520, forall s : _113520 -> Prop, (forall x : _113520, (@IN _113520 x (@INSERT _113520 a s)) -> P x) = ((P a) /\ (forall x : _113520, (@IN _113520 x s) -> P x))).
