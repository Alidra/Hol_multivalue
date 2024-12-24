Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3619179 : forall {A B : Type'}, forall f : A -> B, forall A' : B -> Prop, ((forall x : A, forall y : A, ((f x) = (f y)) -> x = y) /\ (@FINITE B A')) -> @FINITE A (@GSPEC A (fun GEN_PVAR_102 : A => exists x : A, @SETSPEC A GEN_PVAR_102 (@IN B (f x) A') x)).
