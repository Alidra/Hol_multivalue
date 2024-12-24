Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5113408 : forall {A : Type'}, forall lt2 : A -> A -> Prop, ((forall x : A, ~ (lt2 x x)) /\ ((forall x : A, forall y : A, forall z : A, ((lt2 x y) /\ (lt2 y z)) -> lt2 x z) /\ (forall x : A, @FINITE A (@GSPEC A (fun GEN_PVAR_227 : A => exists y : A, @SETSPEC A GEN_PVAR_227 (lt2 y x) y))))) -> @WF A lt2.
