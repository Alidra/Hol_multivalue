Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7932353 : forall {A : Type'}, forall x : tybit1 A, exists a : finite_sum (finite_sum A A) unit, x = (@mktybit1 A a).
