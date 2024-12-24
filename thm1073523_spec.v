Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1073523 : forall {A : Type'}, forall a0' : A, forall a1' : list A, ~ ((@nil A) = (@cons A a0' a1')).
