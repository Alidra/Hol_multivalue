Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4372190 : forall {_104907 : Type'} (f : (_104907 -> Prop) -> Prop) (h1 : ~ (f = (@EMPTY (_104907 -> Prop)))), ~ (f = (@EMPTY (_104907 -> Prop))).
