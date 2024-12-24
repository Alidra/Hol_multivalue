Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem53965 : forall {_5486 _5488 : Type'}, forall P : _5486 -> _5488 -> Prop, (forall x : _5486, forall y : _5488, P x y) = (forall z : prod _5486 _5488, P (@fst _5486 _5488 z) (@snd _5486 _5488 z)).
