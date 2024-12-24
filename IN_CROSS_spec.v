Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4325365 : forall {_103718 _103721 : Type'}, forall x : _103718, forall y : _103721, forall s : _103718 -> Prop, forall t : _103721 -> Prop, (@IN (prod _103718 _103721) (@pair _103718 _103721 x y) (@CROSS _103721 _103718 s t)) = ((@IN _103718 x s) /\ (@IN _103721 y t)).
