Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3580897 : forall {_91760 _91764 _91765 : Type'}, forall P : _91765 -> Prop, forall f : _91765 -> _91760, forall g : _91765 -> _91764, (forall x : _91765, forall y : _91765, ((P x) /\ ((P y) /\ ((g x) = (g y)))) -> (f x) = (f y)) = (exists h : _91764 -> _91760, forall x : _91765, (P x) -> (f x) = (h (g x))).
