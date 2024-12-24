Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3117508 : forall (a : nat) (b : nat), ((fun b' : nat => (num_divides a b') = (int_divides (int_of_num a) (int_of_num b'))) b) = ((num_divides a b) = (int_divides (int_of_num a) (int_of_num b))).
