Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2495588 : forall m : int, forall n : int, forall q : int, forall r : int, ((m = (int_add (int_mul q n) r)) /\ ((int_le (int_of_num (NUMERAL 0)) r) /\ (int_lt r (int_abs n)))) -> ((div m n) = q) /\ ((rem m n) = r).
