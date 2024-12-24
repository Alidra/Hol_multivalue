Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7159247 : forall {A B : Type'}, forall f : A -> B, forall g : A -> real, forall s : A -> Prop, (@FINITE A s) -> (@sum A s g) = (@sum B (@IMAGE A B f s) (fun y : B => @sum A (@GSPEC A (fun GEN_PVAR_324 : A => exists x : A, @SETSPEC A GEN_PVAR_324 ((@IN A x s) /\ ((f x) = y)) x)) g)).
