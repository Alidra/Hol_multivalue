Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem19732 : forall {A : Type'} (P : A -> Prop), forall x : A, (P x) -> P (@ε A P).
