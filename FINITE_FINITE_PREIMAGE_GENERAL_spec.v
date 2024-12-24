Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3617662 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, ((@FINITE B t) /\ (forall y : B, (@IN B y t) -> @FINITE A (@GSPEC A (fun GEN_PVAR_98 : A => exists x : A, @SETSPEC A GEN_PVAR_98 ((@IN A x s) /\ ((f x) = y)) x)))) -> @FINITE A (@GSPEC A (fun GEN_PVAR_99 : A => exists x : A, @SETSPEC A GEN_PVAR_99 ((@IN A x s) /\ (@IN B (f x) t)) x)).
