Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2498022 : forall m : int, forall n : int, forall q : int, forall r : int, ((m = (int_add (int_mul q n) r)) /\ ((int_le (int_of_num (NUMERAL 0)) r) /\ (int_lt r (int_abs n)))) -> (rem m n) = r.
