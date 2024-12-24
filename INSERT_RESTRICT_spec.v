Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3215912 : forall {A : Type'}, forall P : A -> Prop, forall s : A -> Prop, forall a : A, (@GSPEC A (fun GEN_PVAR_8 : A => exists x : A, @SETSPEC A GEN_PVAR_8 ((@IN A x (@INSERT A a s)) /\ (P x)) x)) = (@COND (A -> Prop) (P a) (@INSERT A a (@GSPEC A (fun GEN_PVAR_9 : A => exists x : A, @SETSPEC A GEN_PVAR_9 ((@IN A x s) /\ (P x)) x))) (@GSPEC A (fun GEN_PVAR_10 : A => exists x : A, @SETSPEC A GEN_PVAR_10 ((@IN A x s) /\ (P x)) x))).
