Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem56322 : forall {_5805 _5806 _5807 : Type'}, forall P : _5807 -> _5806 -> _5805 -> Prop, (all (@GABS ((prod _5807 (prod _5806 _5805)) -> Prop) (fun f : (prod _5807 (prod _5806 _5805)) -> Prop => forall x : _5807, forall y : _5806, forall z : _5805, @GEQ Prop (f (@pair _5807 (prod _5806 _5805) x (@pair _5806 _5805 y z))) (P x y z)))) = (forall x : _5807, forall y : _5806, forall z : _5805, P x y z).
