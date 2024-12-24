Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4790437 : forall {_110431 _110433 : Type'}, forall f : _110433 -> _110431, forall l : list _110433, (@set_of_list _110431 (@List.map _110433 _110431 f l)) = (@IMAGE _110433 _110431 f (@set_of_list _110433 l)).
