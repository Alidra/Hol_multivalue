Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7928129 : forall {A : Type'}, forall a : finite_sum A A, forall a' : finite_sum A A, ((@mktybit0 A a) = (@mktybit0 A a')) = (a = a').
