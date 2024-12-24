Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3470554 : forall {_89991 _90000 : Type'}, forall f : _89991 -> _90000, forall s : (_89991 -> Prop) -> Prop, ((~ (s = (@EMPTY (_89991 -> Prop)))) /\ (forall x : _89991, forall y : _89991, ((@IN _89991 x (@UNIONS _89991 s)) /\ ((@IN _89991 y (@UNIONS _89991 s)) /\ ((f x) = (f y)))) -> x = y)) -> (@IMAGE _89991 _90000 f (@INTERS _89991 s)) = (@INTERS _90000 (@IMAGE (_89991 -> Prop) (_90000 -> Prop) (@IMAGE _89991 _90000 f) s)).
