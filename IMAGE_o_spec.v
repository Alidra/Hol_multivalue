Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3370560 : forall {_87566 _87571 _87575 : Type'}, forall f : _87575 -> _87571, forall g : _87566 -> _87575, forall s : _87566 -> Prop, (@IMAGE _87566 _87571 (@o _87566 _87575 _87571 f g) s) = (@IMAGE _87575 _87571 f (@IMAGE _87566 _87575 g s)).
