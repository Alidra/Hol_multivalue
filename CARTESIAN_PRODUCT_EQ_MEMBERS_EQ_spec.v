Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4417723 : forall {_106189 _106193 : Type'}, forall k : _106193 -> Prop, forall s : _106193 -> _106189 -> Prop, forall x : _106193 -> _106189, forall y : _106193 -> _106189, ((@IN (_106193 -> _106189) x (@cartesian_product _106189 _106193 k s)) /\ (@IN (_106193 -> _106189) y (@cartesian_product _106189 _106193 k s))) -> (x = y) = (forall i : _106193, (@IN _106193 i k) -> (x i) = (y i)).
