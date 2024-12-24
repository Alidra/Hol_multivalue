Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem48126 : forall {_4949 _4950 : Type'}, forall P : (prod _4950 _4949) -> Prop, (forall x : _4950, forall y : _4949, P (@pair _4950 _4949 x y)) -> forall p : prod _4950 _4949, P p.
