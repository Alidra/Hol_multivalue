Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7400 : forall {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : forall x : A, (P x) -> Q x), (exists x : A, P x) -> exists x : A, Q x.
