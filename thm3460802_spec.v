Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3460802 : forall {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : _89725 -> _89711 -> Prop), forall x : _89711, (forall t : _89711 -> Prop, (exists x' : _89725, (P x') /\ (t = (f x'))) -> @IN _89711 x t) = (forall x' : _89725, (P x') -> @IN _89711 x (f x')).
