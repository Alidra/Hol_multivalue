Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem9396 : forall {A : Type'} (P : A -> Prop), (ex P) -> P (@ε A P).
