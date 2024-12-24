Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3616275 : forall {A B : Type'}, forall f : A -> B, forall A' : B -> Prop, forall s : A -> Prop, ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@FINITE B A')) -> @FINITE A (@GSPEC A (fun GEN_PVAR_95 : A => exists x : A, @SETSPEC A GEN_PVAR_95 ((@IN A x s) /\ (@IN B (f x) A')) x)).
