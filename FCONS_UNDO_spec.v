Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1066212 : forall {A : Type'}, forall f : nat -> A, f = (@FCONS A (f (NUMERAL 0)) (@o nat nat A f S)).
