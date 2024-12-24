Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3493630 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, (((@SUBSET A (@GSPEC A (fun GEN_PVAR_82 : A => exists x : A, @SETSPEC A GEN_PVAR_82 ((@IN A x u) /\ (@IN B (f x) (@IMAGE A B f s))) x)) s) /\ (@SUBSET A t u)) \/ ((@SUBSET A (@GSPEC A (fun GEN_PVAR_83 : A => exists x : A, @SETSPEC A GEN_PVAR_83 ((@IN A x u) /\ (@IN B (f x) (@IMAGE A B f t))) x)) t) /\ (@SUBSET A s u))) -> (@IMAGE A B f (@INTER A s t)) = (@INTER B (@IMAGE A B f s) (@IMAGE A B f t)).
