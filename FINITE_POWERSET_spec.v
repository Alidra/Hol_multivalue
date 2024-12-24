Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4603107 : forall {A : Type'}, forall s : A -> Prop, (@FINITE A s) -> @FINITE (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_155 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_155 (@SUBSET A t s) t)).
