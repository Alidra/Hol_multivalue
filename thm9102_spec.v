Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem9102 : forall {A : Type'}, forall P : A -> Prop, forall t : A, (forall x : A, (x = t) -> P x) -> ex P.
