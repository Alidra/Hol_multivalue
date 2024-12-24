Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4790171 : forall {_110384 : Type'}, forall x : _110384, forall l : list _110384, (@IN _110384 x (@set_of_list _110384 l)) = (@List.In _110384 x l).
