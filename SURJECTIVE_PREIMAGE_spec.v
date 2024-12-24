Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5056432 : forall {A B : Type'}, forall f : A -> B, (forall k : A -> Prop, exists t : B -> Prop, (@GSPEC A (fun GEN_PVAR_225 : A => exists x : A, @SETSPEC A GEN_PVAR_225 (@IN B (f x) t) x)) = k) = (forall x : A, forall y : A, ((f x) = (f y)) -> x = y).
