Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3617834 : forall {A B : Type'}, forall f : A -> B, forall t : B -> Prop, ((@FINITE B t) /\ (forall y : B, (@IN B y t) -> @FINITE A (@GSPEC A (fun GEN_PVAR_100 : A => exists x : A, @SETSPEC A GEN_PVAR_100 ((f x) = y) x)))) -> @FINITE A (@GSPEC A (fun GEN_PVAR_101 : A => exists x : A, @SETSPEC A GEN_PVAR_101 (@IN B (f x) t) x)).
