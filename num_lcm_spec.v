Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2840178 : forall a : nat, forall b : nat, (num_lcm (@pair nat nat a b)) = (num_of_int (int_lcm (@pair int int (int_of_num a) (int_of_num b)))).
