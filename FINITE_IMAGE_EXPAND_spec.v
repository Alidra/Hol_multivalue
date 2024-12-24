Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3615039 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, (@FINITE A s) -> @FINITE B (@GSPEC B (fun GEN_PVAR_94 : B => exists y : B, @SETSPEC B GEN_PVAR_94 (exists x : A, (@IN A x s) /\ (y = (f x))) y)).
