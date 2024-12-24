Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4597289 : forall {A : Type'}, forall s : A -> Prop, forall n : nat, (@HAS_SIZE A s n) -> @HAS_SIZE (A -> Prop) (@GSPEC (A -> Prop) (fun GEN_PVAR_153 : A -> Prop => exists t : A -> Prop, @SETSPEC (A -> Prop) GEN_PVAR_153 (@SUBSET A t s) t)) (Nat.pow (NUMERAL (BIT0 (BIT1 0))) n).
