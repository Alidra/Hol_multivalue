Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem9425 : forall {A : Type'} (P : A -> Prop), (P (@ε A P)) = (ex P).
