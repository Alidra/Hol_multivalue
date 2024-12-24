Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3368783 : forall {_87504 _87515 : Type'}, forall f : _87504 -> _87515, forall s : _87504 -> Prop, forall t : _87504 -> Prop, (@IMAGE _87504 _87515 f (@UNION _87504 s t)) = (@UNION _87515 (@IMAGE _87504 _87515 f s) (@IMAGE _87504 _87515 f t)).
