Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4372272 : forall {_104908 : Type'} (g : (_104908 -> Prop) -> Prop) (h1 : ~ (g = (@EMPTY (_104908 -> Prop)))), ~ (g = (@EMPTY (_104908 -> Prop))).
