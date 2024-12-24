Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3455583 : forall {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : _89534 -> _89520 -> Prop), forall x : _89520, (exists t : _89520 -> Prop, (exists x' : _89534, (P x') /\ (t = (f x'))) /\ (@IN _89520 x t)) = (exists x' : _89534, (P x') /\ (@IN _89520 x (f x'))).
