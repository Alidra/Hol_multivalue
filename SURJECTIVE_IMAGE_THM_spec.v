Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3588668 : forall {A B : Type'}, forall f : A -> B, (forall y : B, exists x : A, (f x) = y) = (forall P : B -> Prop, (@IMAGE A B f (@GSPEC A (fun GEN_PVAR_89 : A => exists x : A, @SETSPEC A GEN_PVAR_89 (P (f x)) x))) = (@GSPEC B (fun GEN_PVAR_90 : B => exists x : B, @SETSPEC B GEN_PVAR_90 (P x) x))).
