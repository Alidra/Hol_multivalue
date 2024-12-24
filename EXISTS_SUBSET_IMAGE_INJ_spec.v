Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3655226 : forall {_93490 _93497 : Type'}, forall P : (_93497 -> Prop) -> Prop, forall f : _93490 -> _93497, forall s : _93490 -> Prop, (exists t : _93497 -> Prop, (@SUBSET _93497 t (@IMAGE _93490 _93497 f s)) /\ (P t)) = (exists t : _93490 -> Prop, (@SUBSET _93490 t s) /\ ((forall x : _93490, forall y : _93490, ((@IN _93490 x t) /\ (@IN _93490 y t)) -> ((f x) = (f y)) = (x = y)) /\ (P (@IMAGE _93490 _93497 f t)))).
