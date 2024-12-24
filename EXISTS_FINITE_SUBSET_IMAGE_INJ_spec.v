Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3688903 : forall {_93670 _93677 : Type'}, forall P : (_93677 -> Prop) -> Prop, forall f : _93670 -> _93677, forall s : _93670 -> Prop, (exists t : _93677 -> Prop, (@FINITE _93677 t) /\ ((@SUBSET _93677 t (@IMAGE _93670 _93677 f s)) /\ (P t))) = (exists t : _93670 -> Prop, (@FINITE _93670 t) /\ ((@SUBSET _93670 t s) /\ ((forall x : _93670, forall y : _93670, ((@IN _93670 x t) /\ (@IN _93670 y t)) -> ((f x) = (f y)) = (x = y)) /\ (P (@IMAGE _93670 _93677 f t))))).
