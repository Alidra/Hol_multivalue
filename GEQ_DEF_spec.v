Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem44156 : forall {A : Type'}, forall a : A, forall b : A, (@GEQ A a b) = (a = b).
