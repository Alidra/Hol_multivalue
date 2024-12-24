Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3689549 : forall {_93766 _93773 : Type'}, forall P : (_93773 -> Prop) -> Prop, forall f : _93766 -> _93773, forall s : _93766 -> Prop, (forall t : _93773 -> Prop, ((@FINITE _93773 t) /\ (@SUBSET _93773 t (@IMAGE _93766 _93773 f s))) -> P t) = (forall t : _93766 -> Prop, ((@FINITE _93766 t) /\ ((@SUBSET _93766 t s) /\ (forall x : _93766, forall y : _93766, ((@IN _93766 x t) /\ (@IN _93766 y t)) -> ((f x) = (f y)) = (x = y)))) -> P (@IMAGE _93766 _93773 f t)).
