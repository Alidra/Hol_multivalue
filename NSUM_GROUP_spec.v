Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6994742 : forall {A B : Type'}, forall f : A -> B, forall g : A -> nat, forall s : A -> Prop, forall t : B -> Prop, ((@FINITE A s) /\ (@SUBSET B (@IMAGE A B f s) t)) -> (@nsum B t (fun y : B => @nsum A (@GSPEC A (fun GEN_PVAR_296 : A => exists x : A, @SETSPEC A GEN_PVAR_296 ((@IN A x s) /\ ((f x) = y)) x)) g)) = (@nsum A s g).
