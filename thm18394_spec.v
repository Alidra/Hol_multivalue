Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem18394 : forall {A : Type'} (P : A -> Prop), (~ (ex P)) = (forall x : A, ~ (P x)).
