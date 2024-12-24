Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3070443 : forall a : nat, forall b : nat, (int_of_num (num_gcd (@pair nat nat a b))) = (int_gcd (@pair int int (int_of_num a) (int_of_num b))).
