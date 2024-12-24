Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem9221 : forall {A : Type'}, forall P : A -> Prop, forall x : A, (P x) -> P (@ε A P).
