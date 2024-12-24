Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5056129 : forall {A B : Type'}, forall f : A -> B, (forall t : B -> Prop, forall t' : B -> Prop, ((@GSPEC A (fun GEN_PVAR_223 : A => exists x : A, @SETSPEC A GEN_PVAR_223 (@IN B (f x) t) x)) = (@GSPEC A (fun GEN_PVAR_224 : A => exists x : A, @SETSPEC A GEN_PVAR_224 (@IN B (f x) t') x))) -> t = t') = ((@IMAGE A B f (@UNIV A)) = (@UNIV B)).
