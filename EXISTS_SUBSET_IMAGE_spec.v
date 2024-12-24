Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3647316 : forall {_93365 _93381 : Type'}, forall P : (_93381 -> Prop) -> Prop, forall f : _93365 -> _93381, forall s : _93365 -> Prop, (exists t : _93381 -> Prop, (@SUBSET _93381 t (@IMAGE _93365 _93381 f s)) /\ (P t)) = (exists t : _93365 -> Prop, (@SUBSET _93365 t s) /\ (P (@IMAGE _93365 _93381 f t))).
