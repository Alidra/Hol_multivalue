Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4600502 : forall {A : Type'}, forall s : A -> Prop, (@FINITE A s) -> (@CARD (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_154 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_154 (@SUBSET A t s) t))) = (Nat.pow (NUMERAL (BIT0 (BIT1 0))) (@CARD A s)).
