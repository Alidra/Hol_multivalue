Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem51006 : forall {_5131 _5132 : Type'}, forall P : (prod _5132 _5131) -> Prop, (exists p : prod _5132 _5131, P p) = (exists p1 : _5132, exists p2 : _5131, P (@pair _5132 _5131 p1 p2)).
