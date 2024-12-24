Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5047839 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall u : B -> Prop, (forall t : B -> Prop, forall t' : B -> Prop, ((@SUBSET B t u) /\ ((@SUBSET B t' u) /\ ((@GSPEC A (fun GEN_PVAR_220 : A => exists x : A, @SETSPEC A GEN_PVAR_220 ((@IN A x s) /\ (@IN B (f x) t)) x)) = (@GSPEC A (fun GEN_PVAR_221 : A => exists x : A, @SETSPEC A GEN_PVAR_221 ((@IN A x s) /\ (@IN B (f x) t')) x))))) -> t = t') = (@SUBSET B u (@IMAGE A B f s)).
