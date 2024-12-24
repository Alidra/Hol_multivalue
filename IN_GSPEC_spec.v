Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3400493 : forall {A : Type'}, forall s : A -> Prop, (@GSPEC A (fun GEN_PVAR_30 : A => exists x : A, @SETSPEC A GEN_PVAR_30 (@IN A x s) x)) = s.
