Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2611267 : forall a : int, forall b : int, forall c : int, (int_lt (int_of_num (NUMERAL 0)) a) -> (int_lt (div b a) c) = (int_lt b (int_mul a c)).
