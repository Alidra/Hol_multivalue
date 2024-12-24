Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4605019 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (@FINITE A s) -> @FINITE (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_158 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_158 ((@SUBSET A t s) /\ (P t)) t)).
