Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5119703 : forall {A : Type'}, forall s : A -> Prop, (@FINITE A s) -> @WF (A -> Prop) (fun t1 : A -> Prop => fun t2 : A -> Prop => (@PSUBSET A t1 t2) /\ (@SUBSET A t2 s)).
