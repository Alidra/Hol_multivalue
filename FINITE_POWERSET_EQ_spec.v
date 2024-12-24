Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4604266 : forall {A : Type'}, forall s : A -> Prop, (@FINITE (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_156 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_156 (@SUBSET A t s) t))) = (@FINITE A s).
