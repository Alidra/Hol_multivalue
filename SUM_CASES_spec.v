Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7188904 : forall {A : Type'}, forall s : A -> Prop, forall P : A -> Prop, forall f : A -> real, forall g : A -> real, (@FINITE A s) -> (@sum A s (fun x : A => @COND real (P x) (f x) (g x))) = (real_add (@sum A (@GSPEC A (fun GEN_PVAR_328 : A => exists x : A, @SETSPEC A GEN_PVAR_328 ((@IN A x s) /\ (P x)) x)) f) (@sum A (@GSPEC A (fun GEN_PVAR_329 : A => exists x : A, @SETSPEC A GEN_PVAR_329 ((@IN A x s) /\ (~ (P x))) x)) g)).
