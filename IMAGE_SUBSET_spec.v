Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3371475 : forall {_87593 _87604 : Type'}, forall f : _87593 -> _87604, forall s : _87593 -> Prop, forall t : _87593 -> Prop, (@SUBSET _87593 s t) -> @SUBSET _87604 (@IMAGE _87593 _87604 f s) (@IMAGE _87593 _87604 f t).
