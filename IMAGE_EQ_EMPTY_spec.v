Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3385500 : forall {_87928 _87932 : Type'}, forall f : _87932 -> _87928, forall s : _87932 -> Prop, ((@IMAGE _87932 _87928 f s) = (@EMPTY _87928)) = (s = (@EMPTY _87932)).
