Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3581220 : forall {_91790 _91810 _91811 : Type'}, forall f : _91810 -> _91811, forall g : _91810 -> _91790, (forall x : _91810, forall y : _91810, ((g x) = (g y)) -> (f x) = (f y)) = (exists h : _91790 -> _91811, f = (@o _91810 _91790 _91811 h g)).
