Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3488494 : forall {_90535 _90546 : Type'}, forall f : _90535 -> _90546, forall s : _90535 -> Prop, forall t : _90535 -> Prop, @SUBSET _90546 (@IMAGE _90535 _90546 f (@INTER _90535 s t)) (@INTER _90546 (@IMAGE _90535 _90546 f s) (@IMAGE _90535 _90546 f t)).
