Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3655850 : forall {_93578 _93585 : Type'}, forall P : (_93585 -> Prop) -> Prop, forall f : _93578 -> _93585, forall s : _93578 -> Prop, (forall t : _93585 -> Prop, (@SUBSET _93585 t (@IMAGE _93578 _93585 f s)) -> P t) = (forall t : _93578 -> Prop, ((@SUBSET _93578 t s) /\ (forall x : _93578, forall y : _93578, ((@IN _93578 x t) /\ (@IN _93578 y t)) -> ((f x) = (f y)) = (x = y))) -> P (@IMAGE _93578 _93585 f t)).
