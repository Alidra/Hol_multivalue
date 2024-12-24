Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem13690 : forall {_2843 _2845 : Type'}, forall P : _2845 -> Prop, forall R : _2845 -> _2843 -> Prop, (forall x : _2845, (P x) -> exists y : _2843, R x y) = (exists f : _2845 -> _2843, forall x : _2845, (P x) -> R x (f x)).
