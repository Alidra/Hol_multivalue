Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem49909 : forall {_5106 _5107 : Type'}, forall P : (prod _5107 _5106) -> Prop, (forall p : prod _5107 _5106, P p) = (forall p1 : _5107, forall p2 : _5106, P (@pair _5107 _5106 p1 p2)).
