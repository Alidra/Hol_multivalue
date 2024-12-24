Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3199546 : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, (@IMAGE A B f s) = (@GSPEC B (fun GEN_PVAR_7 : B => exists y : B, @SETSPEC B GEN_PVAR_7 (exists x : A, (@IN A x s) /\ (y = (f x))) y)).
