Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4372329 : forall {_104961 : Type'} (f : (_104961 -> Prop) -> Prop) (h1 : f = (@EMPTY (_104961 -> Prop))), f = (@EMPTY (_104961 -> Prop)).
