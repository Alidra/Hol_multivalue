Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5055298 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall u : B -> Prop, (forall k : A -> Prop, (@SUBSET A k s) -> exists t : B -> Prop, (@SUBSET B t u) /\ ((@GSPEC A (fun GEN_PVAR_222 : A => exists x : A, @SETSPEC A GEN_PVAR_222 ((@IN A x s) /\ (@IN B (f x) t)) x)) = k)) = ((@SUBSET B (@IMAGE A B f s) u) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y)).
