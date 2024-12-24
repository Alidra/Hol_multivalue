Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2649536 : forall m : int, forall n : int, forall p : int, ((rem m n) = p) = ((((n = (int_of_num (NUMERAL 0))) /\ (m = p)) \/ ((int_le (int_of_num (NUMERAL 0)) p) /\ (int_lt p (int_abs n)))) /\ (@eq2 int m p (int_mod n))).
