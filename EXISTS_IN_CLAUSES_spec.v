Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5032597 : forall {_113540 _113580 : Type'}, (forall P : _113540 -> Prop, (exists x : _113540, (@IN _113540 x (@EMPTY _113540)) /\ (P x)) = False) /\ (forall P : _113580 -> Prop, forall a : _113580, forall s : _113580 -> Prop, (exists x : _113580, (@IN _113580 x (@INSERT _113580 a s)) /\ (P x)) = ((P a) \/ (exists x : _113580, (@IN _113580 x s) /\ (P x)))).
