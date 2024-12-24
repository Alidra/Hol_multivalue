Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3397302 : forall {_88193 _88202 : Type'}, forall f : _88193 -> _88202, forall s : (_88193 -> Prop) -> Prop, (@IMAGE _88193 _88202 f (@UNIONS _88193 s)) = (@UNIONS _88202 (@IMAGE (_88193 -> Prop) (_88202 -> Prop) (@IMAGE _88193 _88202 f) s)).
