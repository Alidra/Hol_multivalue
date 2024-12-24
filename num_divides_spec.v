Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2836659 : forall a : nat, forall b : nat, (num_divides a b) = (int_divides (int_of_num a) (int_of_num b)).
