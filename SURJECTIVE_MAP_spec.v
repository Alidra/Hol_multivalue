Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1199951 : forall {A B : Type'}, forall f : A -> B, (forall m : list B, exists l : list A, (@List.map A B f l) = m) = (forall y : B, exists x : A, (f x) = y).
