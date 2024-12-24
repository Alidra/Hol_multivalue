Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem44133 : forall {A B : Type'}, forall f : A -> B, forall x : A, (@LET A B f x) = (f x).
