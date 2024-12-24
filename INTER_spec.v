Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3190197 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@INTER A s t) = (@GSPEC A (fun GEN_PVAR_2 : A => exists x : A, @SETSPEC A GEN_PVAR_2 ((@IN A x s) /\ (@IN A x t)) x)).
