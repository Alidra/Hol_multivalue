Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem48811 : forall {A : Type'} (a : A) (b : A), (fun b' : A => (@GEQ A a b') = (a = b')) b.
