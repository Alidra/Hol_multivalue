Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem18898 : forall {A B : Type'} (P : A -> B -> Prop), (fun P' : A -> B -> Prop => (forall x : A, exists y : B, P' x y) = (exists y : A -> B, forall x : A, P' x (y x))) P.
