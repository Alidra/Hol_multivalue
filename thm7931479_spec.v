Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7931479 : forall {A : Type'} (a : finite_sum A A) (a' : finite_sum A A), (fun a'' : finite_sum A A => ((@mktybit0 A a) = (@mktybit0 A a'')) = (a = a'')) a'.
