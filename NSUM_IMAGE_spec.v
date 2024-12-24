Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6961680 : forall {_127560 _127584 : Type'}, forall f : _127584 -> _127560, forall g : _127560 -> nat, forall s : _127584 -> Prop, (forall x : _127584, forall y : _127584, ((@IN _127584 x s) /\ ((@IN _127584 y s) /\ ((f x) = (f y)))) -> x = y) -> (@nsum _127560 (@IMAGE _127584 _127560 f s) g) = (@nsum _127584 s (@o _127584 _127560 nat g f)).
