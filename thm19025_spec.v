Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem19025 : forall {A : Type'} (P : A -> Prop) (Q : Prop), ((fun Q' : Prop => ((forall x : A, P x) /\ Q') = (forall x : A, (P x) /\ Q')) Q) = (((forall x : A, P x) /\ Q) = (forall x : A, (P x) /\ Q)).
