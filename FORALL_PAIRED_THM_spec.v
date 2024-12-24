Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem55507 : forall {_5733 _5734 : Type'}, forall P : _5734 -> _5733 -> Prop, (all (@GABS ((prod _5734 _5733) -> Prop) (fun f : (prod _5734 _5733) -> Prop => forall x : _5734, forall y : _5733, @GEQ Prop (f (@pair _5734 _5733 x y)) (P x y)))) = (forall x : _5734, forall y : _5733, P x y).
