Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem55945 : forall {_5769 _5770 : Type'}, forall P : _5770 -> _5769 -> Prop, (ex (@GABS ((prod _5770 _5769) -> Prop) (fun f : (prod _5770 _5769) -> Prop => forall x : _5770, forall y : _5769, @GEQ Prop (f (@pair _5770 _5769 x y)) (P x y)))) = (exists x : _5770, exists y : _5769, P x y).
