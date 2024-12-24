Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4979609 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, forall P : B -> Prop, forall n : nat, ((@FINITE A s) /\ ((@FINITE B t) /\ (((@CARD A s) = (@CARD B t)) /\ ((@SUBSET B (@IMAGE A B f s) t) /\ ((forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) /\ (@HAS_SIZE A (@GSPEC A (fun GEN_PVAR_217 : A => exists x : A, @SETSPEC A GEN_PVAR_217 ((@IN A x s) /\ (P (f x))) x)) n)))))) -> @HAS_SIZE B (@GSPEC B (fun GEN_PVAR_218 : B => exists x : B, @SETSPEC B GEN_PVAR_218 ((@IN B x t) /\ (P x)) x)) n.
