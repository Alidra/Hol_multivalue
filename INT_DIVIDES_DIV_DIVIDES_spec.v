Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2737101 : forall n : int, forall d : int, forall e : int, ((int_divides d n) /\ ((n = (int_of_num (NUMERAL 0))) -> e = (int_of_num (NUMERAL 0)))) -> (int_divides (div n d) e) = (int_divides n (int_mul d e)).
