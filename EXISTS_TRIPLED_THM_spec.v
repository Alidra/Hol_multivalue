Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem56911 : forall {_5851 _5852 _5853 : Type'}, forall P : _5853 -> _5852 -> _5851 -> Prop, (ex (@GABS ((prod _5853 (prod _5852 _5851)) -> Prop) (fun f : (prod _5853 (prod _5852 _5851)) -> Prop => forall x : _5853, forall y : _5852, forall z : _5851, @GEQ Prop (f (@pair _5853 (prod _5852 _5851) x (@pair _5852 _5851 y z))) (P x y z)))) = (exists x : _5853, exists y : _5852, exists z : _5851, P x y z).
