Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4614687 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, ((@INFINITE A s) /\ (@FINITE B (@IMAGE A B f s))) -> exists a : A, (@IN A a s) /\ (@INFINITE A (@GSPEC A (fun GEN_PVAR_169 : A => exists x : A, @SETSPEC A GEN_PVAR_169 ((@IN A x s) /\ ((f x) = (f a))) x))).
