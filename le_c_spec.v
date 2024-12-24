Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5120869 : forall {_114929 _114934 : Type'}, forall t : _114929 -> Prop, forall s : _114934 -> Prop, (@le_c _114929 _114934 s t) = (exists f : _114934 -> _114929, (forall x : _114934, (@IN _114934 x s) -> @IN _114929 (f x) t) /\ (forall x : _114934, forall y : _114934, ((@IN _114934 x s) /\ ((@IN _114934 y s) /\ ((f x) = (f y)))) -> x = y)).
