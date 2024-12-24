Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1147568 : forall {_26978 _26981 : Type'}, forall f : _26981 -> _26978, forall y : _26978, forall l : list _26981, (@List.In _26978 y (@List.map _26981 _26978 f l)) = (exists x : _26981, (@List.In _26981 x l) /\ (y = (f x))).
