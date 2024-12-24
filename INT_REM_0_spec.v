Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2396893 : forall m : int, (rem m (int_of_num (NUMERAL 0))) = m.
