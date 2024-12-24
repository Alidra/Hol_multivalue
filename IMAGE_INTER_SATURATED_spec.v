Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3556761 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : A -> Prop, ((@SUBSET A (@GSPEC A (fun GEN_PVAR_86 : A => exists x : A, @SETSPEC A GEN_PVAR_86 (@IN B (f x) (@IMAGE A B f s)) x)) s) \/ (@SUBSET A (@GSPEC A (fun GEN_PVAR_87 : A => exists x : A, @SETSPEC A GEN_PVAR_87 (@IN B (f x) (@IMAGE A B f t)) x)) t)) -> (@IMAGE A B f (@INTER A s t)) = (@INTER B (@IMAGE A B f s) (@IMAGE A B f t)).
