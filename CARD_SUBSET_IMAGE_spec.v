Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4018621 : forall {_101783 _101790 : Type'}, forall f : _101783 -> _101790, forall s : _101790 -> Prop, forall t : _101783 -> Prop, ((@FINITE _101783 t) /\ (@SUBSET _101790 s (@IMAGE _101783 _101790 f t))) -> Peano.le (@CARD _101790 s) (@CARD _101783 t).
