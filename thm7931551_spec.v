Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7931551 : forall {A : Type'}, forall x : tybit0 A, exists a : finite_sum A A, x = (@mktybit0 A a).
