Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4617672 : forall {A : Type'}, forall s : A -> Prop, forall n : nat, (@FINITE (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_174 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_174 ((@SUBSET A t s) /\ (@HAS_SIZE A t n)) t))) = ((@FINITE A s) \/ (n = (NUMERAL 0))).
