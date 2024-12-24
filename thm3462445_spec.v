Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3462445 : forall {_89769 _89788 _89789 : Type'} (P : _89789 -> _89788 -> Prop) (f : _89789 -> _89788 -> _89769 -> Prop), forall x : _89769, (forall t : _89769 -> Prop, (exists x' : _89789, exists y : _89788, (P x' y) /\ (t = (f x' y))) -> @IN _89769 x t) = (forall x' : _89789, forall y : _89788, (P x' y) -> @IN _89769 x (f x' y)).
