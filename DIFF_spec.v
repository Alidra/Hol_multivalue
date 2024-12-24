Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3192076 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@DIFF A s t) = (@GSPEC A (fun GEN_PVAR_4 : A => exists x : A, @SETSPEC A GEN_PVAR_4 ((@IN A x s) /\ (~ (@IN A x t))) x)).
