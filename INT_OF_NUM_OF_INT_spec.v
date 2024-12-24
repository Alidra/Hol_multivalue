Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2834258 : forall x : int, (int_le (int_of_num (NUMERAL 0)) x) -> (int_of_num (num_of_int x)) = x.
