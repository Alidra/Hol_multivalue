Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4452626 : forall {_106843 _106845 : Type'}, forall P : _106845 -> _106843 -> Prop, forall k : _106845 -> Prop, forall s : _106845 -> _106843 -> Prop, (~ ((@cartesian_product _106843 _106845 k s) = (@EMPTY (_106845 -> _106843)))) -> (forall i : _106845, forall x : _106843, ((@IN _106845 i k) /\ (@IN _106843 x (s i))) -> P i x) = (forall z : _106845 -> _106843, forall i : _106845, ((@IN (_106845 -> _106843) z (@cartesian_product _106843 _106845 k s)) /\ (@IN _106845 i k)) -> P i (z i)).
