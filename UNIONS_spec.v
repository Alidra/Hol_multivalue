Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3189257 : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@UNIONS A s) = (@GSPEC A (fun GEN_PVAR_1 : A => exists x : A, @SETSPEC A GEN_PVAR_1 (exists u : A -> Prop, (@IN (A -> Prop) u s) /\ (@IN A x u)) x)).
