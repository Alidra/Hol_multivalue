Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem113 : forall {A : Type'} (P : A -> Prop), (@ex1 A P) -> ex P.
