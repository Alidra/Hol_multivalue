Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4106042 : forall {A : Type'}, forall n : nat, forall s : A -> Prop, forall u : A -> Prop, ((@SUBSET A s u) /\ ((@FINITE A s) /\ ((Peano.le (@CARD A s) n) /\ ((@FINITE A u) -> Peano.le n (@CARD A u))))) -> exists t : A -> Prop, (@SUBSET A s t) /\ ((@SUBSET A t u) /\ (@HAS_SIZE A t n)).
