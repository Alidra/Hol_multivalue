Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7362 : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : forall x : A, (P x) -> Q x), (forall x : A, P x) -> forall x : A, Q x.
