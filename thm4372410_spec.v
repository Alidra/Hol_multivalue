Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4372410 : forall {_105011 : Type'} (f : (_105011 -> Prop) -> Prop) (h1 : ~ (f = (@EMPTY (_105011 -> Prop)))), ~ (f = (@EMPTY (_105011 -> Prop))).
