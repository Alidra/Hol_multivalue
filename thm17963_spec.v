Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem17963 : forall {A : Type'} (P : A -> Prop), (fun P' : A -> Prop => (~ (exists x : A, P' x)) = (forall x : A, ~ (P' x))) P.
