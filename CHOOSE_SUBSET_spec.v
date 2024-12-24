Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4086093 : forall {A : Type'}, forall s : A -> Prop, (@FINITE A s) -> forall n : nat, (Peano.le n (@CARD A s)) -> exists t : A -> Prop, (@SUBSET A t s) /\ (@HAS_SIZE A t n).
