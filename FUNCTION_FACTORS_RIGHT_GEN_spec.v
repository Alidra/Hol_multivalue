Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3582879 : forall {_91854 _91858 _91859 : Type'}, forall P : _91859 -> Prop, forall f : _91859 -> _91854, forall g : _91858 -> _91854, (forall x : _91859, (P x) -> exists y : _91858, (g y) = (f x)) = (exists h : _91859 -> _91858, forall x : _91859, (P x) -> (f x) = (g (h x))).
