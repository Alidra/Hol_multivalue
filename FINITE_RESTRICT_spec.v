Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3603906 : forall {A : Type'}, forall s : A -> Prop, forall P : A -> Prop, (@FINITE A s) -> @FINITE A (@GSPEC A (fun GEN_PVAR_91 : A => exists x : A, @SETSPEC A GEN_PVAR_91 ((@IN A x s) /\ (P x)) x)).
