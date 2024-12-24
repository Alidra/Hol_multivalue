Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem48806 : forall {A : Type'} (a : A) (b : A), ((fun b' : A => (a = b') = (@GEQ A a b')) b) = ((a = b) = (@GEQ A a b)).
