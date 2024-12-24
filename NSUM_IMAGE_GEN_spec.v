Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6993167 : forall {A B : Type'}, forall f : A -> B, forall g : A -> nat, forall s : A -> Prop, (@FINITE A s) -> (@nsum A s g) = (@nsum B (@IMAGE A B f s) (fun y : B => @nsum A (@GSPEC A (fun GEN_PVAR_295 : A => exists x : A, @SETSPEC A GEN_PVAR_295 ((@IN A x s) /\ ((f x) = y)) x)) g)).
