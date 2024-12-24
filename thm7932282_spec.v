Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7932282 : forall {A : Type'} (a : finite_sum (finite_sum A A) unit) (a' : finite_sum (finite_sum A A) unit), ((fun a'' : finite_sum (finite_sum A A) unit => ((@mktybit1 A a) = (@mktybit1 A a'')) = (a = a'')) a') = (((@mktybit1 A a) = (@mktybit1 A a')) = (a = a')).
