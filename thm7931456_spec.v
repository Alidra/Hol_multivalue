Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7931456 : forall {A : Type'}, forall a : finite_sum (finite_sum A A) unit, forall a' : finite_sum (finite_sum A A) unit, ((@mktybit1 A a) = (@mktybit1 A a')) = (a = a').
